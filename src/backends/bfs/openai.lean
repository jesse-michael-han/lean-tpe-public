import evaluation
import utils

-- TODO(jesse): code duplication >:(

namespace openai

section openai_api

meta structure CompletionRequest : Type :=
(prompt : string)
(max_tokens : int := 16)
(temperature : native.float := 1.0)
(top_p : native.float := 1)
(n : int := 1)
(best_of : option int := none)
(stream : option bool := none)
(logprobs : int := 0)
(echo : option bool := none)
(stop : option string := none) -- TODO(jesse): list string
(presence_penalty : option native.float := none)
(frequency_penalty : option native.float := none)
(show_trace : bool := ff)
(prompt_token := "PROOFSTEP")
-- don't support logit_bias for now

-- TODO(jesse): write a derive handler for this kind of structure serialization
/-- this is responsible for validating parameters,
   e.g. ensuring floats are between 0 and 1 -/
meta instance : has_to_tactic_json CompletionRequest :=
let validate_max_tokens : int → bool := λ n, n ≤ 2048 in
let validate_float_frac : native.float → bool := λ k, 0 ≤ k ∧ k ≤ 1 in
let validate_and_return {α} [has_to_format α] (pred : α → bool) : α → tactic α :=
  λ a, ((guard $ pred a) *> pure a <|> by {tactic.unfreeze_local_instances, exact (tactic.fail format!"[openai.CompletionRequest.to_tactic_json] VALIDATION FAILED FOR {a}")}) in
let validate_optional_and_return {α} [has_to_format α] (pred : α → bool) : option α → tactic (option α) := λ x, do {
  match x with
  | (some val) := some <$> by {tactic.unfreeze_local_instances, exact (validate_and_return pred val)}
  | none := pure none
  end
} in
let MAX_N : int := 100000 in
let fn : CompletionRequest → tactic json := λ req, match req with
| ⟨prompt, max_tokens, temperature, top_p, n, best_of,
  stream, logprobs, echo, stop, presence_penalty, frequency_penalty, _, _⟩ := do
  -- TODO(jesse): ensure validation does not fail silently
  max_tokens ← validate_and_return validate_max_tokens max_tokens,
  -- temperature ← validate_and_return validate_float_frac temperature,
  top_p ← validate_and_return validate_float_frac top_p,
  n ← validate_and_return (λ x, 0 ≤ x ∧ x ≤ MAX_N) /- go wild with the candidates -/ n,
  best_of ← validate_optional_and_return (λ x, n ≤ x ∧ x ≤ MAX_N) best_of,
  presence_penalty ← validate_optional_and_return validate_float_frac presence_penalty,
  frequency_penalty ← validate_optional_and_return validate_float_frac frequency_penalty,

  eval_trace $ "[openai.CompletionRequest.to_tactic_json] VALIDATION PASSED",

  let pre_kvs : list (string × option json) := [
    ("prompt", json.of_string prompt),
    ("max_tokens", json.of_int max_tokens),
    ("temperature", json.of_float temperature),
    ("top_p", json.of_float top_p),
    ("n", json.of_int n),
    ("best_of", json.of_int <$> best_of),
    ("stream", json.of_bool <$> stream),
    ("logprobs", some $ json.of_int logprobs),
    ("echo", json.of_bool <$> echo),
    ("stop", json.of_string <$> stop),
    ("presence_penalty", json.of_float <$> presence_penalty),
    ("frequency_penalty", json.of_float <$> frequency_penalty)
  ],

  pure $ json.object $ pre_kvs.filter_map (λ ⟨k,mv⟩, prod.mk k <$> mv)
end
in ⟨fn⟩

/-
example from API docs:
curl https://api.openai.com/v1/engines/davinci/completions \
  -H 'Content-Type: application/json' \
  -H 'Authorization: Bearer $OPENAI_API_KEY' \
  -d '{
  "prompt": "Once upon a time",
  "max_tokens": 5
}'
-/
meta def dummy_cr : CompletionRequest :=
{prompt := "Once upon a time", max_tokens := 5, temperature := 1.0, top_p := 1.0, n := 3}

meta def CompletionRequest.to_cmd (engine_id : string) (api_key : string) : CompletionRequest → io (io.process.spawn_args)
| req@⟨prompt, max_tokens, temperature, top_p, n, best_of,
  stream, logprobs, echo, stop, presence_penalty, frequency_penalty, _, _⟩ := do
when EVAL_TRACE $ io.put_str_ln' format!"[openai.CompletionRequest.to_cmd] ENTERING",
serialized_req ← io.run_tactic' $ has_to_tactic_json.to_tactic_json req,
when EVAL_TRACE $ io.put_str_ln' format!"[openai.CompletionRequest.to_cmd] SERIALIZED",
pure {
  cmd := "curl",
  args := [
         "-u"
      , format.to_string $ format!":{api_key}"
      ,  "-X"
      , "POST"
--      ,  format.to_string format!"http://router.api.svc.owl.sci.openai.org:5004/v1/engines/{engine_id}/completions"
      ,  format.to_string format!"https://api.openai.com/v1/engines/{engine_id}/completions"
      , "-H", "OpenAI-Organization: org-kuQ09yewcuHU5GN5YYEUp2hh"
      , "-H", "Content-Type: application/json"
      , "-d"
      , json.unparse serialized_req
    ]
}

setup_tactic_parser

-- nice, it works
-- example {p q} (h₁ : p) (h₂ : q) : p ∧ q :=
-- begin
--   apply and.intro, do {tactic.read >>= postprocess_tactic_state >>= eval_trace}
-- end

meta def serialize_ts
  (req : CompletionRequest)
  : tactic_state → tactic CompletionRequest := λ ts, do {
  ts_str ← ts.fully_qualified >>= postprocess_tactic_state,
  let prompt : string :=
    "[LN] GOAL " ++ ts_str ++ (format! " {req.prompt_token} ").to_string,
  eval_trace format!"\n \n \n PROMPT: {prompt} \n \n \n ",
  pure {
    prompt := prompt,
    ..req}
}

setup_tactic_parser

private meta def decode_response_msg : json → io (json × json) := λ response_msg, do {
  (json.array choices) ← lift_option $ response_msg.lookup "choices" | io.fail' format!"can't find choices in {response_msg}",
  prod.mk <$> (json.array <$> choices.mmap (λ choice, lift_option $ json.lookup choice "text")) <*> do {
    logprobss ← choices.mmap (λ msg, lift_option $ msg.lookup "logprobs"),
    scoress ← logprobss.mmap (λ logprobs, lift_option $ logprobs.lookup "token_logprobs"),
    result ← json.array <$> scoress.mmap (lift_option ∘ json_float_array_sum),
    pure result
  }
}

meta def openai_api (engine_id : string) (api_key : string) : ModelAPI CompletionRequest :=
let fn : CompletionRequest → io json := λ req, do {
  proc_cmds ← req.to_cmd engine_id api_key,
  -- when req.show_trace $ io.put_str_ln' format!"[openai_api] PROC_CMDS: {proc_cmds}",
  response_raw ← io.cmd proc_cmds,
  when req.show_trace $ io.put_str_ln' format!"[openai_api] RAW RESPONSE: {response_raw}",

  response_msg ← (lift_option $ json.parse response_raw) | io.fail' format!"[openai_api] JSON PARSE FAILED {response_raw}",
    
  when req.show_trace $ io.put_str_ln' format!"GOT RESPONSE_MSG",

  -- predictions ← (lift_option $ do {
  --   (json.array choices) ← response_msg.lookup "choices" | none,
  --   /- `choices` is a list of {text: ..., index: ..., logprobs: ..., finish_reason: ...}-/
  --   texts ← choices.mmap (λ choice, choice.lookup "text"),
  --   (scoress : list json) ← choices.mmap (λ msg, msg.lookup "logprobs" >>= λ x, x.lookup "token_logprobs"),
  --   -- scores ← scoress.mmap (λ xs, xs.map (λ msg,
  --   scores ← scoress.mmap json_float_array_sum,
  --   pure $ prod.mk texts scores
  --  }) 

  do {
    predictions ← decode_response_msg response_msg | io.fail' format!"[openai_api] UNEXPECTED RESPONSE MSG: {response_msg}",
    when req.show_trace $ io.put_str_ln' format!"PREDICTIONS: {predictions}",
    pure (json.array [predictions.fst, predictions.snd])
  } <|> pure (json.array $ [json.of_string $ format.to_string $ format!"ERROR {response_msg}"]) -- catch API errors here
} in ⟨fn⟩

end openai_api

section openai_proof_search

meta def read_first_line : string → io string := λ path, do
  buffer.to_string <$> (io.mk_file_handle path io.mode.read >>= io.fs.get_line)

-- in entry point, API key is read from command line and then set as an environment variable for the execution
-- of the command

@[inline, reducible]meta def tab : char := '\t'

@[inline, reducible]meta def newline : char := '\n'

meta def default_partial_req : openai.CompletionRequest :=
{
  prompt := "",
  max_tokens := 128,
  temperature := (0.7 : native.float),
  top_p := 1,
  n := 1,
  best_of := none,
  stream := none,
  logprobs := 0,
  echo := none,
  stop := none, -- TODO(jesse): list string,
  presence_penalty := none,
  frequency_penalty := none,
  show_trace := EVAL_TRACE
}

/- this is the entry point for the evalution harness -/
meta def openai_bfs_proof_search_core
  (partial_req : openai.CompletionRequest)
  (engine_id : string)
  (api_key : string)
  (fuel := 5)
  : state_t BFSState tactic unit := do
monad_lift $ set_show_eval_trace partial_req.show_trace,
bfs_core
  (openai_api engine_id api_key)
    (openai.serialize_ts partial_req)
      (λ msg n, run_all_beam_candidates (unwrap_lm_response_logprobs $ some "[openai_greedy_proof_search_core]") msg n)
        (fuel)

/- for testing API failure handling.
   replace `openai.openai_bfs_proof_search_core` with
   `openai.dummy_openai_bfs_proof_search_core` in
   `evaluation/bfs/gptf.lean` and confirm that the
   produced `.json` files show `api_failures = 1`
-/
meta def dummy_openai_bfs_proof_search_core
  (partial_req : openai.CompletionRequest)
  (engine_id : string)
  (api_key : string)
  (fuel := 5)
  : state_t BFSState tactic unit := do
monad_lift $ set_show_eval_trace partial_req.show_trace,
bfs_core
    dummy_api
    (openai.serialize_ts partial_req)
      (λ msg n, run_all_beam_candidates (unwrap_lm_response_logprobs $ some "[openai_greedy_proof_search_core]") msg n)
        (fuel)

/- meant for interactive use -/
meta def openai_bfs_proof_search
  (partial_req : openai.CompletionRequest)
  (engine_id : string)
  (api_key : string)
  (fuel := 5)
  (verbose := ff)
  (max_width : ℕ := 25)
  (max_depth : ℕ := 50)
  : tactic unit := do
set_show_eval_trace partial_req.show_trace,
bfs
  (openai_api engine_id api_key)
    (openai.serialize_ts partial_req)
      (λ msg n, run_all_beam_candidates (unwrap_lm_response_logprobs $ some "[openai_greedy_proof_search]") msg n)
        (fuel) (verbose) (max_width) (max_depth)

end openai_proof_search

section playground

example : true :=
begin
  trivial
  -- openai_bfs_proof_search default_partial_req "formal-large-lean-webmath-1230-v1-c4" API_KEY
end

-- example : true :=
-- begin
--   openai_greedy_proof_search
--     default_partial_req
--       "formal-large-lean-webmath-1230-v1-c4"
--         API_KEY
-- end

-- example (n : ℕ) (m : ℕ) : nat.succ (n + m) < (nat.succ n + m) + 1  :=
-- begin
--   -- openai_greedy_proof_search
--   --   {n := 10, temperature := 0.7, ..default_partial_req}
--   --     "formal-large-lean-webmath-1230-v1-c4"
--   --       API_KEY 10 tt,
-- sorry
-- -- rw succ_add,  exact nat.lt_succ_self _
-- end

-- theorem t2 (p q r : Prop) (h₁ : p) (h₂ : q) : (q ∧ p) ∨ r :=

-- lemma peirce_identity {P Q :Prop} : ((P → Q) → P) → P :=
-- begin
--   openai_greedy_proof_search
--     {n := 25, temperature := 0.7, ..default_partial_req}
--       "formal-large-lean-webmath-1230-v1-c4"
--         API_KEY 10,
-- end

-- --   openai_greedy_proof_search
-- --     default_partial_req
-- --       "formal-large-lean-webmath-1230-v1-c4"
-- --         API_KEY
-- -- -- simp [or_assoc, or_comm, or_left_comm]

-- end

end playground

end openai
