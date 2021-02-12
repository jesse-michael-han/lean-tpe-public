import evaluation_step
import backends.greedy.fairseq

section main

meta def SEARCH_CORE
  (req : fairseq.CompletionRequest)
  (entry_pt : string) 
  (model_path : string) 
  (data_path : string)
  (fuel : ℕ := 25) :
  state_t GreedyProofSearchState tactic unit :=
  fairseq.fairseq_greedy_proof_search_core req entry_pt model_path data_path fuel

meta def main : io unit := do {
  args ← io.cmdline_args,
  decls_file ← lift_option $ args.nth 0 | io.fail "must supply decls_file as first argument",
  dest ← lift_option $ args.nth 1 | io.fail "must supply dest as second argument",
  max_tokens ← string.to_nat <$> (lift_option $  args.nth 2) | io.fail "must supply max tokens",
  (some temperature) ← (native.float.of_string <$> (lift_option $ args.nth 3)) | io.fail "must supply temperature",
  nbest ← string.to_nat <$> (lift_option $ args.nth 4) | io.fail "must supply nbest",
  beam ← string.to_nat <$> (lift_option $ args.nth 5) | io.fail "must supply beam",
  fuel ← string.to_nat <$> (lift_option $ args.nth 6) | io.fail "must supply fuel",
  entry_pt ← lift_option $ args.nth 7 | io.fail "must supply entry point",
  model_path ← lift_option $ args.nth 8 | io.fail "must supply model path",
  data_path ← lift_option $ args.nth 9 | io.fail "must supply data path",
  tac_timeout ← string.to_nat <$> args.nth_except 10 "tac_timeout",
  global_timeout ← string.to_nat <$> args.nth_except 11 "global_timeout",

  let req : fairseq.CompletionRequest := {
    max_tokens := max_tokens,
    temperature := temperature,
    nbest := nbest,
    beam := beam,
    ..fairseq.default_partial_req
  },

  -- let register_task_id : GreedyProofSearchState → string → GreedyProofSearchState :=
  --   λ σ task_id, {task_id := task_id, ..σ},
  evaluation_harness_from_decls_file (SEARCH_CORE req entry_pt model_path data_path fuel) decls_file dest global_timeout $ pure {tac_timeout := tac_timeout}
}

end main
