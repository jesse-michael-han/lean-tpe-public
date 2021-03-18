/-
Copyright (c) 2020 Jason Rute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Jason Rute and Jesse Michael Han

REPL for interacting with Lean
-/
import data.nat.basic
import system.io
import tactic.core
import tactic

import utils
import .tactic_state
import basic.queue

section tactic_state
open interaction_monad.result
setup_tactic_parser

/- set this to tt to enable tracing
  `tactic.set_bool_option` is tactic state specific,
  and is difficult to globally set -/

meta def num_goals' : tactic_state → option ℕ :=
λ ts, match tactic.num_goals ts with | (success val _) := pure val | _ := none end

-- TODO(jesse): this is a hack. might be better to do this in python
meta def consume_with_parser {α} (p : lean.parser α) : string → io string := λ inp, do {
  io.run_tactic' $ do
    prod.snd <$> (lean.parser.run_with_input (with_input p inp) "")
}

-- TODO(jesse): performance
meta def consume_spaces : string → string
| arg@⟨[]⟩ := arg
| arg@⟨(x::xs)⟩ := if x = ' ' then consume_spaces ⟨xs⟩ else arg

-- WARNING: this is a hack
meta def remove_indents_with_split (c : char := '\t'): string → string := λ str,
let strs := str.split (= '\t') in
string.intercalate (⟨['\t']⟩ : string) (consume_spaces <$> strs)

meta def postprocess_tactic_state : tactic_state → tactic string := λ ts, do
  let main : tactic string := do {
    let ts_str := ts.to_format.to_string,
    tabbed_ts_str ← do {
      if (num_goals' ts).get_or_else 0 ≤ 1
      then pure $ ts_str.replace_char '\n' '\t'
      else tactic.unsafe_run_io $ (λ x, string.replace_char x '\n' '\t')
             <$> (consume_with_parser small_nat >=>
               consume_with_parser ident) ts_str},
    pure $ remove_indents_with_split '\t' tabbed_ts_str
  },
  main <|> (let msg := "[postprocess_tactic_state] WARNING: POSTPROCESSING FAILED" in tactic.trace msg *> tactic.fail msg)

end tactic_state

meta def add_open_namespace : name → tactic unit := λ nm, do
env ← tactic.get_env, tactic.set_env (env.execute_open nm)

meta def add_open_namespaces (nms : list name) : tactic unit :=
nms.mmap' add_open_namespace

section run_with_state'

namespace interaction_monad
open interaction_monad.result
meta def run_with_state' {σ₁ σ₂ : Type} {α : Type*} (state : σ₁) (tac : interaction_monad σ₁ α) : interaction_monad σ₂ α :=
λ s, match (tac state) with
     | (success val _) := success val s
     | (exception fn pos _) := exception fn pos s
     end
end interaction_monad
end run_with_state'

namespace tactic

open interaction_monad.result
meta def run (tac : tactic unit) : tactic (interaction_monad.result tactic_state unit) := do {
  σ ← get_state,
  match tac σ with
  | r@(success _ new_state) := interaction_monad.set_state new_state *> pure r
  | r@(exception fn pos new_state) := pure r
  end
}

-- meta instance has_format_result {α σ} [has_to_format σ] [has_to_format α] : has_to_format (interaction_monad.result σ α) := ⟨by mk_to_format `interaction_monad.result⟩ -- ayyy

meta instance has_to_format_tactic_result {α : Type*} [has_to_format α] : has_to_format (interaction_monad.result tactic_state α) :=
⟨λ r,
  match r with
  | (success val new_state) := format!"SUCCESS!\nNEW_STATE: {new_state}\nVAL: {val}"
  | (exception fn pos old_state) := do {
    let msg := (fn.get_or_else (λ _, format.of_string "n/a")) (),
    format!"EXCEPTION!\nMSG: {msg}\nPOS: {pos}\nOLD_STATE: {old_state}"
  }
  end
⟩

meta instance has_to_tactic_format_tactic_result {α : Type*} [has_to_format α] : has_to_tactic_format (interaction_monad.result tactic_state α) :=
⟨λ σ, pure $ has_to_format.to_format σ⟩

end tactic

section parse_eval_tac
setup_tactic_parser
open tactic

meta def parse_eval_tac
  (ps : parser_state)
  (tactic_string : string)
  : tactic (tactic unit × format) := do {
  let itactic_string := "{" ++ tactic_string ++ "}",
  texpr ← (reflected_value.expr ∘ prod.fst) <$>
    (interaction_monad.run_with_state' ps $ with_input parser.itactic_reflected itactic_string),
  prod.mk <$> (eval_expr (tactic unit) texpr) <*> has_to_tactic_format.to_tactic_format texpr
}

end parse_eval_tac

section frontend

open tactic lean lean.parser interactive
meta def read_eval_print_loop (ps : parser_state) : tactic unit :=
do
  trace "\nTactic state:",
  trace_state,
  let rest : tactic unit := do
  {trace "\nEnter a tactic command:",
  tactic_string <- tactic.unsafe_run_io $ io.get_line,
  (t, fmt) ← parse_eval_tac ps tactic_string,
  trace "",
  trace ("Running tactic:\n" ++ fmt.to_string),
  tactic.run t >>= eval_trace,  -- runs the tactic on the goal.  It is crashing
  read_eval_print_loop},  --- loops forever
  done <|> rest

--- like main_t, but sets the goal and environment to a user-supplied theorem in mathlib
--- note: if the environment contains all declarations in mathlib,
--- and olean files exist,
--- we don't need to supply the lean file as env.decl_olean will find it automatically.
meta def main_t_at : parser_state → tactic unit := λ ps, do {
  trace "enter declaration to prove",
  goal_nm_string ← tactic.unsafe_run_io $ io.get_line,
  ⟨nm, _⟩ ← interaction_monad.run_with_state' ps $ with_input ident goal_nm_string,
  env ← get_env,
  decl ← env.get nm,
  let g := decl.type,
  set_goal_to g,
  lean_file ← env.decl_olean nm,
  set_env_core $ environment.for_decl_of_imported_module lean_file nm,
  read_eval_print_loop ps
}

@[user_command]
meta def main_app_at
(meta_info : decl_meta_info) (_ : parse (tk "main_app_at")) : lean.parser unit :=
get_state >>= of_tactic ∘ (main_t_at)

end frontend

section main

setup_tactic_parser

open tactic
meta def main_t : parser_state → tactic unit := λ ps,
do
  trace "Enter a goal:",
  set_goal_to `(true),
  goal_string <- tactic.unsafe_run_io $ io.get_line,
  trace "GOAL STRING: " *> trace goal_string,
  (goal_pexpr, _) ← interaction_monad.run_with_state' ps $ with_input types.texpr goal_string,
  eval_trace ps.cur_pos,
  set_goal_to <e> goal_pexpr,
  (read_eval_print_loop ps) *> main_t ps  -- loops forever

@[user_command]
meta def main_app
(meta_info : decl_meta_info) (_ : parse (tk "main_app")) : lean.parser unit :=
(get_state >>= of_tactic ∘ main_t)

end main

section parse_tac

setup_tactic_parser

open tactic

/-- Parse a reflected interactive tactic from a string.
    The result can be evaluated to a `tactic unit` by using
    `eval_expr (tactic unit)`. -/
meta def parse_itactic_reflected (tactic_string : string) : tactic expr :=
let itactic_string := "{ " ++ tactic_string ++  " }" in
lean.parser.run $ do
  get_state >>= λ ps, of_tactic $ do
    tactic.set_env ps.env,
    -- eval_trace format!"[parse_itactic_reflected] TRYING TO PARSE {itactic_string}",
    (reflected_value.expr ∘ prod.fst) <$>
      (@interaction_monad.run_with_state' parser_state _ _ ps $
         with_input parser.itactic_reflected itactic_string)

/-- Parse an interactive tactic from a string. -/
meta def parse_itactic (tactic_string : string) : tactic (tactic unit) := do
  rtac ← parse_itactic_reflected tactic_string,
  eval_expr (tactic unit) rtac

end parse_tac

section evaluation_harness

meta def run_tac_with_tactic_state
  (tac : tactic unit)
  (ts : tactic_state)
  : tactic (result _ _) := do {
  tactic.write ts,
  pure $ tac ts
}

meta structure EvaluationInput : Type :=
(decl_nm : name)
(ts_data : tactic_state_data)
(tactic_string : string)
(open_namespaces : list name)

/- (before_state, action, after_state) tuple -/
meta structure EvaluationResult : Type :=
(before_state : tactic_state)
(tactic_string : string)
(result : result tactic_state unit)

meta instance : has_to_format EvaluationResult :=
⟨λ ⟨σ, tac_str, r⟩,
  format.join [
    -- hmm. why doesn't the highlighting work?
    format.highlight "INPUT STATE:\n" format.color.pink,
    σ.to_format,
    "\n\n",
    format.highlight "ACTION:\n" format.color.pink,
    tac_str,
    "\n\n",
    format.highlight  "RESULT:\n" format.color.pink,
    (has_to_format.to_format r)
  ]
⟩

/-- Creates an empty tactic state. -/
meta def mk_tactic_state : tactic tactic_state :=
tactic.unsafe_run_io $ io.run_tactic' $ tactic.exact `(trivial) *> tactic.read

/-- creates tactic_state_data as if we were proving the declaration
 (currently only theorems are supported) with name `decl_nm`. -/
meta def get_tsd_at_decl (decl_nm : name) : tactic tactic_state_data := do {
  env ← tactic.get_env,
  decl ← env.get decl_nm,
  mk_tactic_state >>= tactic.write,
  ts ← tactic.read,
  tactic.set_goal_to decl.type,
  result ← tactic_state_data.get,
  tactic.write ts,
  pure result
}

meta def run_evaluation : EvaluationInput → tactic EvaluationResult :=
λ ⟨decl, ts_data, tactic_string, ns⟩, (tactic.unsafe_run_io ∘ io.run_tactic') $ do {
  tac ← parse_itactic tactic_string,
  env ← get_env_at_decl decl,
  tactic.set_env_core env,
  add_open_namespaces ns,
  ts ← rebuild_tactic_state ts_data *> tactic.read,
  EvaluationResult.mk ts tactic_string <$> run_tac_with_tactic_state tac ts
}

section greedy_proof_search

meta structure ModelAPI (input_format : Type := json) : Type :=
(query : input_format → io json)

/- for testing -/
meta def dummy_api {α} : ModelAPI α :=
⟨λ _, pure $ json.of_string "[DummyAPI] FAILURE"⟩

namespace tactic
open interaction_monad interaction_monad.result

/- capture but backtrack the state -/
meta def capture' {α} (t : tactic α) : tactic (tactic_result α) :=
λ s, match t s with
| (success r s') := success (success r s') s
| (exception f p s') := success (exception f p s') s
end

end tactic

meta def tactic_hash : tactic ℕ := do {
  gs ← tactic.get_goals,
  hs ← gs.mmap $ λ g, do {
    tactic.set_goal_to g,
    es ← (::) <$> tactic.target <*> tactic.local_context,
    pure $ es.foldl (λ acc e, acc + e.hash) 0},
  pure $ hs.sum
}

meta def compare_tactic_state : tactic_state → tactic_state → tactic bool := λ ts₁ ts₂, do {
  ts ← tactic.read,
  h₁ ← (tactic.write ts₁ *> tactic_hash),
  h₂ ← (tactic.write ts₂ *> tactic_hash),
  tactic.write ts,
  pure $ h₁ = h₂
}
    -- let done_handler : state_t GreedyProofSearchState tactic bool := do {
    --   state_t.lift $ do {
    --     tactic.done,
    --     tactic.result >>= (λ x, tactic.guard_sorry x <|>
    --       eval_trace format! "[greedy_proof_search_step] WARNING: result contains sorry" *> tactic.failed),
    --     tactic.result >>= (λ x, tactic.type_check x <|>
    --       eval_trace format! "[greedy_proof_search_step] WARNING: result failed typechecking" *> tactic.failed)
    --   },

meta def validate_proof (pf : expr) : tactic unit := do {
  let tac (e : expr) : tactic unit := do {
    mk_tactic_state >>= tactic.write,
    guard (bnot pf.has_meta_var),
    tactic.guard_sorry e,
    tactic.type_check e
  },
  result ← tactic.capture' (tac pf),
  match result with
  | (interaction_monad.result.success r s') := pure ()
  | (interaction_monad.result.exception f p s') := tactic.fail "[validate_proof] ERROR: VALIDATION FAILED"
  end
}

meta def tactic_state.is_done (state : tactic_state) : tactic bool := do {
  ts ← tactic.read,
  result_flag ← do {
    tactic.write state,
    (do {
       tactic.done *> pure tt
     }) <|> pure ff
  },
  tactic.write ts,
  pure result_flag
}

meta def tactic_result.is_done {α} (tr : tactic_result α) : tactic bool := do {
  match tr with
  | (interaction_monad.result.success val state) := state.is_done
  | (interaction_monad.result.exception _ _ _) := pure ff
  end
}

meta def get_tac_and_capture_result (next_candidate : string) (timeout : ℕ := 5000) : tactic (tactic_result unit) := do {
  tac ← do {
    env ← tactic.get_env,
    eval_trace format!"[get_tac_and_capture_result] PARSING TACTIC: {next_candidate}",
    tac ← parse_itactic next_candidate,
    eval_trace format!"[get_tac_and_capture_result] PARSE SUCCESSFUL",
    tactic.set_env env,
    pure tac
  },
  eval_trace format!"[get_tac_and_capture_result] TRYING TACTIC: {next_candidate}",
  result ← tactic.capture' (tactic.try_for_time timeout $ tactic.try_for 200000 tac), -- if `tac` fails, exception is captured here
  eval_trace format!"[get_tac_and_capture_result] RESULT: {result}",

  /- use tactic state hashing to fail on no-ops modulo permutation -/
  result ← match result with
    | (interaction_monad.result.success val ts') := do {
        ts ← tactic.read,
        mcond (compare_tactic_state ts ts')
        (pure $ interaction_monad.mk_exception "tactic state no-op" none ts')
        (pure result)
      }
    | exc := pure exc
  end,
  pure result
}

meta def try_get_tac_and_capture_result (tac_string : string) (timeout : ℕ := 5000) : tactic (tactic_result unit) := do {
  get_tac_and_capture_result tac_string timeout <|> do {
    let msg : format := format!"[try_get_tac_and_capture_result] parse_itactic failed on {tac_string}",
    eval_trace msg,
    interaction_monad.mk_exception msg none <$> tactic.read
  }
}

-- caller of this function is responsible for inspecting results and stopping the search
meta def run_all_beam_candidates
  (get_candidates : json → tactic (list (string × native.float)))
  (msg : json)
  (tac_timeout : ℕ := 5000)
  : tactic (list (tactic_result unit × string × native.float) × list string) := do {

  let try_candidate_state := (list (string × native.float) × (list $ option $ tactic_result unit × string × native.float)),
  let stop : option (tactic_result unit × string × native.float) → state_t try_candidate_state tactic bool :=
    λ arg, match arg with
    | some ⟨result, candidate⟩ := do {
      state_t.lift result.is_done
    }
    | none := pure ff
    end,

  /- TODO(jesse): get rid of this state_t and just use `run_async <$> ...` instead -/
  let try_candidate : state_t try_candidate_state tactic (option $ tactic_result unit × string × native.float) := do {
    state_t.lift $ eval_trace format!"[try_candidate] ENTERING",
    ts ← state_t.lift tactic.read,
    state_t.lift $ eval_trace format!"[try_candidate] READ TACTIC STATE",
    ⟨rest, _⟩ ← state_t.get,
    match rest with
    | [] := do {
      state_t.lift $ eval_trace format!"[try_candidate] END OF LOOP",
      pure $ some ⟨interaction_monad.fail "all candidates failed" ts, "FAILURE", 0.0⟩
    }
    | (next_candidate::candidates) := do  {
      state_t.modify (λ ⟨_, rs⟩, ⟨candidates, rs⟩),
      result ← monad_lift $ try_get_tac_and_capture_result next_candidate.fst tac_timeout,
      when (interaction_monad.result.is_success $ result) $
        state_t.modify $ λ ⟨candidates, rs⟩, ⟨candidates, rs ++ [some $ ⟨result, next_candidate⟩]⟩,
      state_t.lift $ eval_trace format!"[try_candidate] CAPTURED RESULT: {result}",
      pure $ some ⟨result, next_candidate⟩
    }
    end
  },

  -- let find_successful_candidates
  --   (candidates : list (string × native.float))
  --   : tactic (list (tactic_result unit × string × native.float)) := do {
  --   tasks ← candidates.mmap (λ arg, flip prod.mk arg <$> tactic.run_async (try_get_tac_and_capture_result arg.fst : tactic $ tactic_result unit)),
  --   tactic.using_new_ref ff $ λ flag, do 
  --   tasks.iterM [] $ λ acc ⟨task, tac_string, score⟩, do {
  --     mcond (tactic.read_ref flag) (pure acc) $ do {
  --       let result := task.get,
  --       if (interaction_monad.result.is_success result) then do {
  --         whenM (result.is_done) $ tactic.write_ref flag tt,
  --         pure $ acc ++ [⟨result, tac_string, score⟩]
  --       } else do {
  --         pure acc
  --       }
  --     }
  --   }
  -- },

  -- this is responsible for gracefully handling "error" JSON messages and should return an empty list of candidates
  unwrapped_candidates ← get_candidates msg,
  -- eval_trace format!"[run_all_beam_candidates] UNWRAPPED CANDIDATES: {unwrapped_candidates}",
  dedup_unwrapped_candidates ← list.dedup' unwrapped_candidates,
  eval_trace format!"[run_all_beam_candidates] DEDUP_UNWRAPPED CANDIDATES: {dedup_unwrapped_candidates}",
  let candidates := list.filter (λ x, ¬ "tidy".is_prefix_of (prod.fst x)) dedup_unwrapped_candidates,
  
  eval_trace format!"[run_all_beam_candidates] CANDIDATES: {candidates}",
  -- old failure callback
  -- let failure_callback := do {
  -- -- do ts ← state_t.lift tactic.read, pure ⟨interaction_monad.fail "all candidates failed" ts, "FAILURE", 0.0⟩
  -- }
  -- 
  successful_candidates ← (prod.snd <$> prod.snd <$> state_t.run (iterate_until try_candidate stop candidates.length $ pure none) ⟨candidates, []⟩),
  -- successful_candidates ← find_successful_candidates candidates,
  eval_trace format!"[run_all_beam_candidates] EXITING TRY_CANDIDATE LOOP",
  eval_trace format!"[run_all_beam_candidates] SUCCESSFUL CANDIDATES: {successful_candidates}",
  pure ⟨successful_candidates.filter_map id, prod.fst <$> candidates⟩
}

meta def run_best_beam_candidate
  (get_candidates : json → tactic (list string))
  (msg : json)
  (tac_timeout : ℕ := 5000)
  : tactic (tactic_result unit × string × list string) := do {
  let try_candidates : state_t (list string) tactic ((tactic_result unit) × string) := do {
      ts ← state_t.lift (tactic.read),
      (next_candidate::candidates) ← state_t.get | pure (interaction_monad.fail "all candidates failed" ts, "FAILURE"),
      state_t.modify (λ _, candidates),
      flip prod.mk next_candidate <$> (state_t.lift $ try_get_tac_and_capture_result next_candidate tac_timeout)

      -- let get_tac_and_capture_result : state_t (list string) tactic ((tactic_result unit) × string) := do {
      -- tac ← state_t.lift $ do {
      --     env ← tactic.get_env,
      --     eval_trace format!"[run_best_beam_candidate] PARSING TACTIC: {next_candidate}",
      --     tac ← parse_itactic next_candidate, -- this is the only possible point of program failure
      --     eval_trace format!"[run_best_beam_candidate] PARSE SUCCESSFUL",
      --     tactic.set_env env,
      --     pure tac
      --   },
      --   state_t.lift $ do
      --     eval_trace format!"[run_best_beam_candidate] TRYING TACTIC: {next_candidate}",
      --     result ← tactic.capture' (tactic.try_for 200000 tac), -- if `tac` fails, exception is captured here
      --     eval_trace format!"[run_best_beam_candidate] RESULT: {result}",

      --     result ← match result with
      --     | (interaction_monad.result.success val ts') := do {
      --       ts ← tactic.read,
      --       -- ite ((format.to_string $ has_to_format.to_format ts) = (format.to_string $ has_to_format.to_format ts'))
      --       mcond (compare_tactic_state ts ts')
      --        (pure $ interaction_monad.mk_exception "tactic state no-op" none ts')
      --        (pure result)
      --     }
      --     | exc := pure exc
      --     end,
      --     pure ⟨result, next_candidate⟩
      -- },
      -- get_tac_and_capture_result <|> -- handle `parse_itactic` failure here
      --   let msg : format := format!"[run_best_beam_candidate.try_candidates] parse_itactic failed on {next_candidate}" in do
      --   state_t.lift (eval_trace msg),
      --   (pure ⟨interaction_monad.mk_exception
      --     msg none ts, next_candidate⟩)
  },
  let stop : tactic_result unit × string → state_t (list string) tactic bool :=
    pure ∘ interaction_monad.result.is_success ∘ prod.fst,
  candidates ← list.filter (λ x, ¬ "tidy".is_prefix_of x) <$> (get_candidates msg >>= list.dedup),
  eval_trace format!"[run_best_beam_candidate] CANDIDATES: {candidates}",
  try_candidates_result@⟨result, tac_string⟩ ← ((prod.fst <$> state_t.run (iterate_until try_candidates stop) candidates) <|>
  do {
       old_state ← tactic.read,
       pure (prod.mk (interaction_monad.mk_exception "all candidates failed" none old_state) "all failed")
  }),
  eval_trace format!"[run_best_beam_candidate] TRY_CANDIDATES_RESULT: {try_candidates_result}",
  pure ⟨result, tac_string, candidates⟩
}

-- TODO(jesse): finalize JSON format for serialize_ts/decode_response protocol
meta structure GreedyProofSearchState : Type :=
(depth : ℕ := 0)
(tactics : list string := [])
(predictions : list (list string) := [])
(states : list tactic_state := []) -- TODO(jesse): this might make the logs extremely verbose
(success : bool := ff)
(all_failed : bool := ff)
(task_id : string := "")
(global_timeout : bool := ff)
(tac_timeout : ℕ := 5)
(fuel_exhausted : bool := ff)
(decl_goal : string := "")

attribute [derive has_to_format] GreedyProofSearchState

meta instance : has_mark_global_timeout GreedyProofSearchState :=
⟨λ σ, {global_timeout := tt, ..σ}⟩

meta instance : has_register_task_id GreedyProofSearchState :=
⟨λ σ task, {task_id := task, ..σ}⟩

meta instance : has_set_tac_timeout GreedyProofSearchState :=
⟨λ σ timeout, {tac_timeout := timeout, ..σ}⟩

meta instance : has_get_tac_timeout GreedyProofSearchState :=
⟨GreedyProofSearchState.tac_timeout⟩

meta instance : has_mark_fuel_exhausted GreedyProofSearchState :=
⟨λ σ, {fuel_exhausted := tt, ..σ}⟩

meta instance : has_register_decl_goal GreedyProofSearchState :=
⟨λ σ decl_goal, {decl_goal := decl_goal, ..σ}⟩

meta def serialize_list_string : list string → json := λ xs,
  json.array $ json.of_string <$> xs

-- we supply our own instance since the default derive handler is too verbose
meta instance : has_to_tactic_json GreedyProofSearchState :=
let fn : GreedyProofSearchState → tactic json := λ σ, do {
  (serialized_states : list string) ← do {
    σ.states.mmap postprocess_tactic_state
  },
  pure $ json.object $
  [
      ("depth", json.of_int σ.depth)
    , ("tactics", serialize_list_string σ.tactics)
    , ("predictions", json.array $ serialize_list_string <$> σ.predictions)
    -- store only pretty-printed tactic states for now, with newlines replaced by tabs
    , ("states", json.array $ json.of_string <$> serialized_states)
    , ("success", json.of_bool σ.success)
    , ("all_failed", json.of_bool σ.all_failed)
    , ("task_id", json.of_string σ.task_id)
    , ("global_timeout", json.of_bool σ.global_timeout)
    , ("fuel_exhausted", json.of_bool σ.fuel_exhausted)
    , ("decl_goal", json.of_string σ.decl_goal)
  ]
} in ⟨fn⟩

namespace GreedyProofSearchState

meta def add_tac : GreedyProofSearchState → string →  GreedyProofSearchState :=
λ σ tac, {tactics := σ.tactics ++ [tac], ..σ}

meta def bump_depth : GreedyProofSearchState → GreedyProofSearchState :=
λ σ, {depth := nat.succ σ.depth, ..σ}

meta def add_prediction : GreedyProofSearchState → list string → GreedyProofSearchState :=
λ σ pred, {predictions := σ.predictions ++ [pred], ..σ}

meta def add_state : GreedyProofSearchState → tactic_state → GreedyProofSearchState :=
λ σ ts, {states := σ.states ++ [ts], ..σ}

meta def mark_all_failed : GreedyProofSearchState → GreedyProofSearchState :=
λ σ, {all_failed := tt, ..σ}

end GreedyProofSearchState

meta def greedy_proof_search_step
  {input_format : Type}
  (api : ModelAPI input_format)
  (serialize_ts : tactic_state → tactic input_format)
   -- note(jesse): this is responsible for e.g. selecting a candidate from the beam
  (decode_response : json → ℕ → tactic (tactic_result unit × string × list string))
  : state_t GreedyProofSearchState tactic (bool × GreedyProofSearchState) := do {
  state_t.lift $ eval_trace "[greedy_proof_search_step] ENTERING",
  let handle_response (response : tactic_result unit × string × list string) : state_t GreedyProofSearchState tactic unit :=
     match response with | response@⟨result, tac_string, candidates⟩ :=  do {
       if not result.is_success
       then do {
         -- let msg := format!"[greedy_proof_search_step.handle_response] UNEXPECTED
         --   interaction_monad.result.exception: {result}",
         -- eval_trace msg *> tactic.fail msg
         modify $ λ σ, σ.mark_all_failed,
         old_state ← state_t.lift $ tactic.read,
         modify $ λ σ, σ.add_state old_state,
         modify $ λ σ, σ.add_prediction candidates
       }
       else do {
         (interaction_monad.result.success _ ts) ← pure result,
         -- state_t.lift $ tactic.unsafe_run_io $ io.run_tactic' $ _
         modify $ λ σ, σ.bump_depth,
         modify $ λ σ, σ.add_tac tac_string,
         modify $ λ σ, σ.add_prediction candidates,
         old_state ← state_t.lift $ tactic.read,
         modify $ λ σ, σ.add_state old_state
       }
     }
     end,

  let get_response_and_resume : state_t GreedyProofSearchState tactic bool := do {
    tac_timeout_seconds ← GreedyProofSearchState.tac_timeout <$> get,
    response@⟨result, tac_string, candidates⟩ ← state_t.lift $ do {
      ts_msg ← tactic.read >>= serialize_ts,
      eval_trace "[greedy_proof_search_step] QUERYING API",
      response_msg ← tactic.unsafe_run_io $ api.query ts_msg,
      eval_trace format!"[greedy_proof_search_step] RESPONSE MSG {response_msg}",
      eval_trace format!"[greedy_proof_search_step] RUNNING DECODE RESPONSE WITH TIMEOUT {tac_timeout_seconds*1000}",
      response ← decode_response response_msg $ tac_timeout_seconds*1000,
      pure response
    },
    state_t.lift $ eval_trace "[greedy_proof_search_step] HANDLING RESPONSE",
    handle_response response,
    state_t.lift $ eval_trace "[greedy_proof_search_step] HANDLED RESPONSE",
    state_t.lift $ do {
      eval_trace format!"DECODED RESPONSE: {result}",
      when result.is_success $ tactic.resume result,
      eval_trace format!"RESUMED"
    },

    let done_handler : state_t GreedyProofSearchState tactic bool := do {
      state_t.lift $ do {
        tactic.done,
        tactic.result >>= (λ x, tactic.guard_sorry x <|>
          eval_trace format! "[greedy_proof_search_step] WARNING: result contains sorry" *> tactic.failed),
        tactic.result >>= (λ x, tactic.type_check x <|>
          eval_trace format! "[greedy_proof_search_step] WARNING: result failed typechecking" *> tactic.failed)
      },
      modify $ λ σ, {success := tt, ..σ},
      pure tt
    } <|> pure ff,

    let tactic_exception_handler : state_t GreedyProofSearchState tactic bool := do {
      pure (bnot result.is_success)
    },

    done_flag ← done_handler,
    exception_flag ← tactic_exception_handler,
    pure (done_flag || exception_flag)

  },

  done_flag ← get_response_and_resume,

  -- let done_handler : state_t GreedyProofSearchState tactic bool := do {
  --   state_t.lift done,
  --   modify $ λ σ, {success := tt, ..σ},
  --   pure tt
  -- },

  -- done_flag ← done_handler <|> pure ff,

  state_t.lift $ eval_trace format! "DONE FLAG: {done_flag}",

  -- pure ⟨done_flag⟩
  prod.mk done_flag <$> get  /- in second branch, no predictions succeeded and the proof search halts early -/
}

/- TODO(jesse): record proof search state + search statistics; wrap this in a state_t -/
/- `decode_response` should not modify the tactic state and currently
    should only return successful `tactic_result`s -/
/-
   in the full BFS case, `decode_response` should return a list of
   `tactic_result unit`s, which may be ```success` or `exception`
   these should then be logged by the `handle_response` function in
   `greedy_proof_search_step`, and the successful applications
   should be added to the search queue.
-/
meta def greedy_proof_search_core
  {input_format : Type}
  (api : ModelAPI input_format)
  (serialize_ts : tactic_state → tactic input_format)
  (decode_response : json → ℕ → tactic (tactic_result unit × string × list string))
  (fuel := 100000)
  : state_t GreedyProofSearchState tactic unit :=
  let fuel_exhausted_callback : state_t GreedyProofSearchState tactic (bool × GreedyProofSearchState) := do {
    state_t.modify has_mark_fuel_exhausted.mark_fuel_exhausted,
    prod.mk ff <$> get
  } in
  iterate_until
    (greedy_proof_search_step api serialize_ts decode_response)
      (λ x, pure $ x.fst = tt)
        fuel
          fuel_exhausted_callback *> pure ()

meta def greedy_proof_search
  {input_format : Type}
  (api : ModelAPI input_format)
  (serialize_ts : tactic_state → tactic input_format)
  (decode_response : json → ℕ → tactic (tactic_result unit × string × list string))
  (fuel := 100000)
  (verbose := ff)
  : tactic unit := do {
  ⟨_, σ⟩ ← state_t.run (greedy_proof_search_core api serialize_ts decode_response fuel) {},
  when verbose $ eval_trace σ
}

end greedy_proof_search


section bfs

meta structure BFSNode : Type :=
(state : tactic_state)
(score : ℤ := 0)
(tactics : list string := [])
(depth : ℕ := 0)

attribute [derive has_to_format] BFSNode

namespace BFSNode

meta def of_current_state (score : ℤ := 0) (tacs : list string := []) : tactic BFSNode := do {
  ts ← tactic.read,
  pure $ ⟨ts, score, tacs, 0⟩
}

end BFSNode

meta structure BFSState : Type :=
(depth : ℕ := 0)
(num_queries : ℕ := 0)
(tactics : list string := [])
(predictions : list (list string) := [])
(states : list tactic_state := []) -- TODO(jesse): this might make the logs extremely verbose
(success : bool := ff)
(all_failed : bool := ff)
(task_id : string := "")
(max_width : ℕ := 25) -- max qsize
(max_depth : ℕ := 50)
(nodes : pqueue BFSNode.score := pqueue.empty)
(api_failure_count : ℕ := 0)
(all_failed_count : ℕ := 0)
(global_timeout : bool := ff)
(tac_timeout : ℕ := 5)
(fuel_exhausted : bool := ff)
(decl_goal : string := "")

attribute [derive has_to_format] BFSState

meta instance : has_mark_global_timeout BFSState :=
⟨λ σ, {global_timeout := tt, ..σ}⟩

meta instance : has_register_task_id BFSState :=
⟨λ σ task, {task_id := task, ..σ}⟩

meta instance : has_set_tac_timeout BFSState :=
⟨λ σ timeout, {tac_timeout := timeout, ..σ}⟩

meta instance : has_mark_fuel_exhausted BFSState :=
⟨λ σ, {fuel_exhausted := tt, ..σ}⟩

meta instance : has_get_tac_timeout BFSState :=
⟨BFSState.tac_timeout⟩

meta instance : has_register_decl_goal BFSState :=
⟨λ σ decl_goal, {decl_goal := decl_goal, ..σ}⟩

-- meta instance : has_to_tactic_json GreedyProofSearchState :=
-- let fn : GreedyProofSearchState → tactic json := λ σ, do {
--   let serialize_list_string : list string → json := λ xs,
--     json.array $ json.of_string <$> xs,
--   (serialized_states : list string) ← do {
--     σ.states.mmap postprocess_tactic_state
--   },
--   pure $ json.object $
--   [
--       ("depth", json.of_int σ.depth)
--     , ("tactics", serialize_list_string σ.tactics)
--     , ("predictions", json.array $ serialize_list_string <$> σ.predictions)
--     -- store only pretty-printed tactic states for now, with newlines replaced by tabs
--     , ("states", json.array $ json.of_string <$> serialized_states)
--     , ("success", json.of_bool σ.success)
--     , ("all_failed", json.of_bool σ.all_failed)
--     , ("task_id", json.of_string σ.task_id)
--   ]
-- } in ⟨fn⟩

-- TODO(jesse): upgrade to full instance
meta instance : has_to_tactic_json BFSState :=
let fn : BFSState → tactic json := λ σ, do {
  (serialized_states : list string) ← do {
    σ.states.mmap $ λ x, tactic.with_full_names $ postprocess_tactic_state x
  },
  pure $ json.object
  [
      ("depth", json.of_int (σ.depth))
    , ("tactics", json.array $ (json.of_string <$> σ.tactics))
    -- , ("predictions", json.array $ serialize_list_string <$> σ.predictions)
    , ("states", json.array $ json.of_string <$> serialized_states)
    , ("success", json.of_bool (σ.success))
    , ("num_queries", json.of_int (σ.num_queries))
    , ("task_id", json.of_string $ σ.task_id)
    , ("api_failure_count", json.of_int $ σ.api_failure_count)
    , ("all_failed_count", json.of_int $ σ.all_failed_count)
    , ("global_timeout", json.of_bool (σ.global_timeout))
    , ("fuel_exhausted", json.of_bool σ.fuel_exhausted)
    , ("decl_goal", json.of_string σ.decl_goal)
  ]
}
in ⟨fn⟩

section BFSState
namespace BFSState

meta def register_task_id : BFSState → string → BFSState :=
 λ σ task_id, {task_id := task_id, ..σ}

meta def bump_num_queries : BFSState → BFSState :=
λ σ, {num_queries := nat.succ σ.num_queries, ..σ}

meta def push_nodes : BFSState → list BFSNode → BFSState :=
λ σ nodes, {nodes := σ.nodes.enqueue_many nodes, ..σ}

meta def push_node : BFSState → BFSNode → BFSState := λ S σ, S.push_nodes [σ]

meta def add_tac : BFSState → string → BFSState :=
λ σ tac, {tactics := σ.tactics ++ [tac], ..σ}

meta def add_tacs : BFSState → list string → BFSState :=
λ σ tacs, {tactics := σ.tactics ++ tacs, ..σ}

meta def bump_depth : BFSState → BFSState :=
-- λ ⟨d, tacs, preds⟩, ⟨nat.succ d, tacs, preds⟩
λ σ, {depth := nat.succ σ.depth, ..σ}

meta def add_prediction : BFSState → list string → BFSState :=
-- λ ⟨d, tacs, preds⟩ pred, ⟨d, tacs, preds ++ [pred]⟩
λ σ pred, {predictions := σ.predictions ++ [pred], ..σ}

meta def add_state : BFSState → tactic_state → BFSState :=
λ σ ts, {states := σ.states ++ [ts], ..σ}

meta def mark_all_failed : BFSState → BFSState :=
λ σ, {all_failed := tt, ..σ}

meta def mark_success : BFSState → BFSState :=
λ σ, {success := tt, ..σ}

meta def of_current_state (score : ℤ := 0) (max_width : ℕ := 25) (max_depth : ℕ := 50) (tac_timeout : ℕ := 5000) : tactic BFSState := do {
  init_node ← BFSNode.of_current_state score,
  pure {nodes := pqueue.empty.enqueue init_node, max_width := max_width, max_depth := max_depth, tac_timeout := tac_timeout}
}

meta def bump_api_failure_count : BFSState → BFSState :=
λ σ, {api_failure_count := σ.api_failure_count + 1, ..σ}

meta def bump_all_failed_count : BFSState → BFSState :=
λ σ, {all_failed_count := σ.all_failed_count + 1, ..σ}

end BFSState
end BFSState

meta def score_of_float : native.float → int :=
λ x, native.float.floor ((1000.0 : native.float) * x)

meta def pop_node : state_t BFSState tactic BFSNode := do {
  tss ← BFSState.nodes <$> get,
  match tss.dequeue with
  | (some (next, new_nodes)) := do {
      modify $ λ S, {nodes := new_nodes, ..S},
      pure next
    }
  | none := state_t.lift ∘ tactic.fail $ format!"[pop_node] pqueue empty"
  end
}

/-
  Each step of BFS does the following:
    - pops a node off the queue
    - expands the node, producing a list of descendant nodes
    - if any descendant node represents a completed proof search,
      extract the result and use it to fill the main goal
      - this is accomplished by setting the tactic state
-/

meta def bfs_step
  {input_format : Type}
  (api : ModelAPI input_format)
  (serialize_ts : tactic_state → tactic input_format)
   -- note(jesse): this is responsible for e.g. selecting a candidate from the beam
  (decode_response : json → ℕ → tactic (list (tactic_result unit × string × native.float) × list string))
  : state_t BFSState tactic (bool × BFSState) := do {
  σ ← get,
  state_t.lift $ eval_trace format!"[bfs_step] ENTERING, QUEUE STATE: {σ.nodes}",

  (some next_node) ← (some <$> pop_node <|> pure none) | (state_t.lift $ eval_trace format!"[bfs_step] queue empty") *> pure ⟨tt, σ⟩, -- yikes

  ts ← state_t.lift $ tactic.read,

  state_t.lift $ tactic.write next_node.state,

  let handle_response
    (response : list (tactic_result unit × string × native.float) × (list string))
    : state_t BFSState tactic unit :=
     match response with | response@⟨successes, candidates⟩ :=  do {
       modify $ λ σ, σ.add_prediction candidates,
       modify $ λ σ, σ.bump_num_queries,
       when (successes.length = 0) $ modify $ λ σ, σ.bump_all_failed_count,
       when (candidates.length = 0) $ modify $ λ σ, σ.bump_api_failure_count
       -- successes.mmap' $ λ ⟨result, tac_string, score⟩, do {
       --   pure ()
       -- }
     }
     end,

  let get_response_and_resume : state_t BFSState tactic bool := do {
    -- TODO(jesse): `successes` needs to be generalized from `string` to an arbitrary datatype `α`
    -- for the best-first case. for now, we just score everything 0 to get this working
    tac_timeout_seconds ← BFSState.tac_timeout <$> get,
    decl_nm ← BFSState.task_id <$> get,
    response@⟨successes, candidates⟩ ← state_t.lift $ do {
      ts_msg ← tactic.read >>= serialize_ts,
      eval_trace "[bfs_step] QUERYING API",
      response_msg ← tactic.unsafe_run_io $ api.query ts_msg,
      eval_trace format!"[bfs_step] RESPONSE MSG {response_msg}",
      eval_trace format!"[bfs_step] RUNNING DECODE RESPONSE WITH TAC_TIMEOUT {tac_timeout_seconds * 1000}",
      
      do {env ← tactic.get_env, d ← env.get decl_nm, tactic.trace format! "[run_proof_search_step] WARNING: GOT DECL {decl_nm}"} <|> do {tactic.trace format! "[run_proof_search_step] NO GOT DECL {decl_nm}"},
      decoded_response@⟨successes, _⟩ ← decode_response response_msg $ tac_timeout_seconds * 1000,
      eval_trace $ format!"[bfs_step] SUCCESSFUL CANDIDATES: {successes}",
      pure decoded_response
    },
    handle_response response,

    -- turn the successes into a list of new BFSNodes
    (new_nodes : list BFSNode) ← successes.mmap (λ ⟨tr, tac, score⟩, match tr with
      | (interaction_monad.result.success _ state) := do {
        -- assumes that higher float score is better
        let scale_factor := (-100000.0 : native.float),
        let int_score : int := native.float.floor $ (score * scale_factor) + next_node.score,
        pure $ BFSNode.mk state int_score (next_node.tactics ++ [tac]) (next_node.depth + 1)
      }
      | exc := state_t.lift (tactic.fail format!"[bfs_step] UNEXPECTED TACTIC RESULT WHEN CONVERTING TO new_nodes: {exc}")
      end
    ),

    monad_lift $ eval_trace format! "[bfs_step] NODES BEFORE SORTING: {new_nodes}",

    let new_nodes : list BFSNode := @list.merge_sort _ (λ x y : BFSNode, x.score < y.score) _ new_nodes,

    monad_lift $ eval_trace format! "[bfs_step] NODES AFTER SORTING: {new_nodes}",

    /- loop through the new nodes. if any of them are finished (no open goals),
       the proof search is done. otherwise, we add all of them to the BFSState pqueue
       and continue the search.
    -/

    -- modify (λ σ, σ.push_nodes new_nodes),

    -- for_ new_nodes $ λ ⟨state, score⟩, do {

    -- }
    let BFSM := state_t BFSState tactic,
    let push_node_state := (list BFSNode),

    /- note(jesse): this version of `push_node_state_tac` does not quite replicate
      the behavior of greedy_proof_search at
      max_width := 1, because it will loop over all the successful candidates anyways and check
      if the proof is finished regardless of the state of the queue
    -/

    -- let push_node_state_tac : state_t push_node_state BFSM (option BFSNode) := do {
    --   (next_node::xs) ← get | pure none,
    --   done_flag ← state_t.lift $ state_t.lift $ next_node.state.is_done,

    --   result ← if done_flag then pure (some next_node) else do {
    --     q ← BFSState.nodes <$> state_t.lift get,
    --     let qsize := q.size,
    --     state_t.lift $ state_t.lift $ eval_trace format!"[push_tac] QSIZE: {qsize}",
    --     state_t.lift $ state_t.lift $ eval_trace format!"[push_tac] QUEUE: {q}",
    --     size_exceeded ← (do σ ← state_t.lift get,
    --       pure $ to_bool $ (σ.max_width <= σ.nodes.size ∨ σ.max_depth < next_node.tactics.length)),

    --     -- TODO(jesse): more informative trace message
    --     -- TODO(jesse): currently we are erasing open tactic_states which exceed the depth limit.
    --     -- consider storing them in a pqueue of "frozen" nodes instead, and display them in the trace
    --     when size_exceeded $ monad_lift $ eval_trace format!"[push_tac] SIZE EXCEEDED",
    --     unless size_exceeded $ do {
    --       state_t.lift $ state_t.lift $ eval_trace format!"[push_tac] PUSHING NODE",
    --       state_t.lift $ state_t.modify (λ σ, σ.push_node next_node)
    --     },
    --     pure none
    --   },
    --   state_t.modify (λ _, xs),
    --   pure result
    -- },

    /- 
      note(jesse): this version of `push_node_state_tac` checks that the queue is OK
      before proceeding with the rest of the loop
      currently, if max_width := 0 (this is an off-by-one misnomer), this
      reproduces the logic of greedy_proof_search.
    -/
    let push_node_state_tac : state_t push_node_state BFSM (option BFSNode) := do {
      limits_exceeded ← do {
        σ ← state_t.lift get,
        pure $ to_bool $ (σ.max_width < σ.nodes.size ∨ σ.max_depth < next_node.tactics.length)
      },
      
     if limits_exceeded then do {
       monad_lift $ eval_trace format!"[push_tac] SIZE EXCEEDED",
       pure none
     } else do {
       (next_node::xs) ← get | pure none,
       done_flag ← monad_lift $ next_node.state.is_done,
       if done_flag then pure (some next_node) else do {
         q ← BFSState.nodes <$> state_t.lift get,
         let qsize := q.size,
         -- monad_lift $ eval_trace format!"[push_tac] QSIZE: {qsize}",
         -- monad_lift $ eval_trace format!"[push_tac] QUEUE: {q}",
         -- monad_lift $ eval_trace format!"[push_tac] PUSHING NODE",
         state_t.lift $ do {
           state_t.modify (λ σ : BFSState, σ.push_node next_node),
           state_t.modify $ λ σ,
             if σ.depth < next_node.depth then {depth := next_node.depth, ..σ} else σ

           /- note(jesse, January 22 2021, 01:08 AM) temporarily disabling for faster evals -/
           -- state_t.modify $ λ σ, σ.add_state next_node.state -- TODO(jesse): store previous states per-node, not globally
         },
         state_t.modify (λ _, xs),
         pure none
       }
     }
    },

    (done_node) ← prod.fst <$>
      state_t.run
        (iterate_until
          push_node_state_tac
            (pure ∘ option.is_some)
              (new_nodes.length) (pure none)) new_nodes,

    match done_node with
    | (some node) := do {
      state_t.lift $ tactic.write node.state,
      state_t.modify (λ σ, σ.mark_success),
      state_t.modify (λ σ, σ.add_tacs node.tactics),
      pure tt
    }
    | none := pure ff
    end
  },
  done_flag ← get_response_and_resume,
  state_t.lift $ eval_trace format! "DONE FLAG: {done_flag}",

  -- if we are done, then the state has already been set to the successful one
  -- otherwise, backtrack to the original state
  unlessM (pure done_flag) $ state_t.lift (tactic.write ts),
  prod.mk done_flag <$> get
}

meta def bfs_core
  {input_format : Type}
  (api : ModelAPI input_format)
  (serialize_ts : tactic_state → tactic input_format)
  (decode_response : json → ℕ → tactic (list (tactic_result unit × string × native.float) × list string))
  (fuel := 100000)
  : state_t BFSState tactic unit :=
  let fuel_exhausted_callback : state_t BFSState tactic (bool × BFSState) := do {
    state_t.modify has_mark_fuel_exhausted.mark_fuel_exhausted,
    prod.mk ff <$> get
  } in do {
    ts₀ ← monad_lift $ tactic.read,
    [g] ← monad_lift $ tactic.get_goals,
    iterate_until
      (bfs_step api serialize_ts decode_response)
        (λ x, pure $ x.fst = tt)
          fuel
            fuel_exhausted_callback *> pure (),
    σ ← get,
    when σ.success $
    do {pf ← monad_lift $ tactic.get_assignment g >>= tactic.instantiate_mvars,
    (monad_lift (do {-- tactic.set_goals [g], 
    pf ← tactic.get_assignment g >>= tactic.instantiate_mvars,
    tgt ← tactic.infer_type pf,
    ts₁ ← tactic.read,
    tactic.write ts₀, -- important to backtrack to the old state for validation
    validate_proof pf,
    tactic.write ts₁
    }) <|>
      (do monad_lift (eval_trace "[bfs_core] WARNING: VALIDATE_PROOF FAILED"),
       modify $ λ σ, {success := ff, ..σ}))
    }
  }

meta def bfs
  {input_format : Type}
  (api : ModelAPI input_format)
  (serialize_ts : tactic_state → tactic input_format)
  (decode_response : json → ℕ → tactic (list (tactic_result unit × string × native.float) × list string))
  (fuel := 100000)
  (verbose : bool := ff)
  (max_width : ℕ := 25)
  (max_depth : ℕ := 50)
  : tactic unit := do
  init_state ← BFSState.of_current_state 0 max_width max_depth,
  σ ← prod.snd <$> state_t.run (bfs_core api serialize_ts decode_response fuel) init_state,
  when verbose $ eval_trace σ

end bfs

namespace io.process

meta instance : has_to_format spawn_args :=
⟨λ args, args.cmd ++ " " ++ string.intercalate " " args.args⟩

end io.process


section run_proof_search

-- warning: do not use, buggy
meta def try_import (m : module_info.module_name) : tactic unit := do
let env := environment.from_imported_module_name m,
env.fold (pure () : tactic unit) (λ decl acc, acc *> tactic.try (tactic.add_decl decl))

meta def run_proof_search_step
  {search_state : Type}
  (search_core : state_t search_state tactic unit)
  (decl_nm : name)
  (open_ns : list name)
  (show_trace : bool)
  (global_timeout : ℕ)
  (init_state : tactic search_state)
  [has_mark_global_timeout search_state]
  [has_register_decl_goal search_state]
  : io (search_state × string) := do
  io.run_tactic' $ do {
    tsd ← get_tsd_at_decl decl_nm,
    eval_trace format!"[run_proof_search_step] GOT TSD AT DECL {decl_nm}",
    --- set the environment at decl
    env ← get_env_at_decl decl_nm,
    eval_trace format!"[run_proof_search_step] GOT ENV AT DECL {decl_nm}",
    tactic.set_env_core env,
    eval_trace format!"[run_proof_search_step] SET ENV AT DECL {decl_nm}",

    add_open_namespaces open_ns,
    eval_trace format!"[run_proof_search_step] ADDED OPEN NAMESPACES {open_ns}",

    /- note(jesse, January 14 2021, 09:52 AM): commented out because now we should always have namespaces in the .names files -/
    -- additionally open namespaces in decl_nm
    -- for_ decl_nm.components
    --   (λ nm, do env ← tactic.get_env, when (env.is_namespace nm) $
    --      (eval_trace format! "[run_proof_search_step] ADDING OPEN NAMESPACE {nm}") *>
    --        add_open_namespace nm),

    -- eval_trace "[run_proof_search_step] GOT TSD",


    -- eval_trace format!"[run_proof_search_step] SET ENV AT DECL {decl_nm}",
    rebuild_tactic_state tsd,
    eval_trace format!"[run_proof_search_step] REBUILT TACTIC STATE, ENTERING SEARCH CORE WITH TIMEOUT {global_timeout * 1000}",
    decl_goal_string ← format.to_string <$> (tactic.target >>= tactic.pp),
    tactic.read >>= λ ts, eval_trace format!"[run_proof_search_step] TACTIC STATE BEFORE SEARCH CORE: {ts}",
    env ← tactic.get_env,
    do {d ← env.get decl_nm, tactic.trace "[run_proof_search_step] WARNING: GOT DECL"} <|> do {tactic.trace "[run_proof_search_step] NO GOT DECL"},
    σ₀ ← flip has_register_decl_goal.register_decl_goal decl_goal_string <$> init_state,
    σ ← (prod.snd <$> tactic.try_for_time (global_timeout * 1000) (state_t.run (search_core) σ₀) <|> do {
      eval_trace format!"[run_proof_search_step] GLOBAL TIMEOUT REACHED, ABORTING ",
      pure (has_mark_global_timeout.mark_global_timeout σ₀)
    }),
    -- pure $ {task_id := decl_nm.to_string, ..σ}
    pure ⟨σ, decl_nm.to_string⟩
  }

-- to be called in an environment which imports all declarations in `mathlib`
-- ideally called on a shard of the test theorems
meta def run_proof_search_core
  {search_state : Type}
  [has_to_tactic_json search_state]
  (search_core : state_t search_state tactic unit)
  (decl_nms : list (name × list name))
  (process_search_state : search_state → io unit)
  (show_trace : bool)
  (global_timeout : ℕ) -- seconds
  -- (register_task_id : search_state → string → search_state)
  [has_register_task_id search_state]
  [has_mark_global_timeout search_state]
  [has_register_decl_goal search_state]
  (init_state : tactic search_state)
  : io unit := do {
    let run_proof_search_core_body : name → list name → io unit := λ decl_nm open_ns, do {
      when (decl_nm.length > 0) $ do
      when show_trace $ io.put_str_ln' format!"[run_proof_search_core] OUTER LOOP: PROCESSING DECL {decl_nm}",
      env₀ ← io.run_tactic' $ tactic.get_env,
      when show_trace $ io.put_str_ln' format!"[run_proof_search_core] GOT ENV",
      ⟨search_state, decl_nm⟩ ← (run_proof_search_step search_core decl_nm open_ns show_trace global_timeout init_state),
      let search_state := has_register_task_id.register_task_id search_state decl_nm,
      when show_trace $ io.put_str_ln' format!"[run_proof_search_core] GOT SEARCH STATE",
      io.run_tactic' $ tactic.set_env_core env₀,
      process_search_state search_state
    },

    for_ decl_nms (λ ⟨decl_nm, open_ns⟩, do
      run_proof_search_core_body decl_nm open_ns <|> io.put_str_ln' format!"[run_proof_search_core] WARNING: SKIPPING {decl_nm}"
)}

end run_proof_search

end evaluation_harness


section playground

-- example : ℤ → bool
-- | (of_int k) := if
-- set_option pp.notation false
-- #reduce (-3 : ℤ)

-- example (x : ℕ) : nat.zero.gcd x = x :=
-- begin
--   simp [nat.gcd]
-- end

end playground
