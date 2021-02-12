/-
  Runs theorem naming evaluation.
-/

import all
import backends.bfs.openai
import utils.util
import evaluation

section main

meta structure TheoremNamingEvalResult : Type :=
(decl_nm : name) -- name of top-level theorem (i.e. ground truth)
(decl_tp : expr) -- goal of top-level theorem
(predictions : list (string × native.float)) -- sorted list of predictions

meta instance : has_to_tactic_json TheoremNamingEvalResult :=
let fn : Π (σ : TheoremNamingEvalResult), tactic json := λ σ, match σ with
| ⟨nm, tp, preds⟩ := do {
  tp_msg ← json.of_string <$> format.to_string <$> format.flatten <$> tactic.pp tp,
  let pred_msg : json := json.array $ preds.map (λ ⟨candidate_name, score⟩, json.array $ [candidate_name, score]),
  pure $ json.object $ [
      ("name", nm.to_string)
    , ("type", tp_msg)
    , ("predictions", pred_msg)
  ]
}
end
in ⟨fn⟩
open openai

meta def autoname_core (e : expr) (req : CompletionRequest) (engine_id : string) (api_key : string) : tactic (list $ string × native.float) := do {
  ts_str ← format.to_string <$> format.flatten <$> (tactic.with_full_names $ tactic.pp e),
  let prompt : string := "[LN] GOAL " ++ ts_str ++ (format!" {req.prompt_token} ").to_string,
  let completion_request := {prompt := prompt, ..req},
  response_msg ← tactic.unsafe_run_io $ (openai_api engine_id api_key).query completion_request,
  responses ←
    ((list.qsort (λ x y : string × native.float, prod.snd x > prod.snd y) <$>
      unwrap_lm_response_logprobs "autonamer" response_msg) -- >>= list.dedup'
      ),
  eval_trace format! "[autoname_core] RESPONSES: {responses}",
  pure responses
}

meta def get_theorem_naming_result
  (decl_nm : name)
  (decl_tp : expr)
  (req : openai.CompletionRequest)
  (engine_id : string)
  (api_key : string)
  : tactic TheoremNamingEvalResult := do {
  predictions ← autoname_core decl_tp req engine_id api_key,
  pure $ {decl_nm := decl_nm, decl_tp := decl_tp, predictions := predictions}
}

meta def theorem_naming_eval_core
  (decls_file : string)
  (dest : string)
  (engine_id : string)
  (api_key : string)
  (req : openai.CompletionRequest)
  : io unit := do {
  nm_strs ← (io.mk_file_handle decls_file io.mode.read >>= λ f,
  (string.split (λ c, c = '\n') <$> buffer.to_string <$> io.fs.read_to_end f)),

  -- io.put_str_ln' format!"NM STRS: {nm_strs}",

  (nms : list (name × list name)) ← (nm_strs.filter $ λ nm_str, string.length nm_str > 0).mmap $ λ nm_str, do {
    ((io.run_tactic' ∘ parse_decl_nm_and_open_ns) $ nm_str)
  },  
  io.put_str_ln' format!"[theorem_naming_eval_core] GOT {nms.length} NAMES",

  let nms_unfiltered_len := nms.length,
  nms ← io.run_tactic' $ do {
    env ← tactic.get_env,
    nms.mfilter $ λ ⟨nm, _⟩, (do {
      decl ← env.get nm,
      pure decl.is_theorem
    } <|> pure ff)
  },

  io.put_str_ln' format! "[evaluation_harness_from_decls_file] WARNING: SKIPPING {nms_unfiltered_len - nms.length}",

  dest_handle ← io.mk_file_handle dest io.mode.write,

  let process_result : TheoremNamingEvalResult → io unit := λ result, do {
    msg ← json.unparse <$> (io.run_tactic' $ has_to_tactic_json.to_tactic_json result),
    io.fs.put_str_ln_flush dest_handle msg
  },
  for_ nms $ λ ⟨nm, _⟩, do {
    tp ← io.run_tactic' $ do {
      env ← tactic.get_env,
      decl ← env.get nm,
      pure $ decl.type
    },
    result ← io.run_tactic' $ get_theorem_naming_result nm tp req engine_id api_key,
    process_result result
  }
}

/--
  Loops through all the names in `names_file`, queries the model given by `engine_id` for `n` completions,
  and records the predictions
-/
meta def main : io unit := do {
  args ← io.cmdline_args,
  decls_file ← args.nth_except 0 "decls_file",
  dest ← args.nth_except 1 "dest",
  max_tokens ← string.to_nat <$> args.nth_except 2 "max_tokens",
  (some temperature) ← (native.float.of_string <$> (args.nth_except 3 "temperature")) | io.fail "failed to parse temperature",
  (some top_p) ← (native.float.of_string <$> (args.nth_except 4 "top_p")) | io.fail "failed to parse top_p",
  n ← string.to_nat <$> args.nth_except 5 "n",
  best_of ← string.to_nat <$> args.nth_except 6 "best_of",
  fuel ← string.to_nat <$> args.nth_except 7 "fuel",
  max_width ← string.to_nat <$> args.nth_except 8 "max_width",
  max_depth ← string.to_nat <$> args.nth_except 9 "max_depth",
  engine_id ← args.nth_except 10 "engine_id",
  api_key ← args.nth_except 11 "api_key",
  tac_timeout ← string.to_nat <$> args.nth_except 12 "tac_timeout in seconds",
  global_timeout ← string.to_nat <$> args.nth_except 13 "global_timeout in seconds",

  let req : openai.CompletionRequest := {
    max_tokens := max_tokens,
    temperature := temperature,
    top_p := top_p,
    n := n,
    best_of := best_of,
    prompt_token := "PREDICTNAME",
    ..openai.default_partial_req
  },

  theorem_naming_eval_core decls_file dest engine_id api_key req
  -- evaluation_harness_from_decls_file (SEARCH_CORE req engine_id api_key fuel)
  --   decls_file dest global_timeout
  --    $ BFSState.of_current_state 0 max_width max_depth tac_timeout
}
end main
