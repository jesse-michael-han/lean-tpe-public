import evaluation_step
import backends.bfs.fairseq

section main

meta def SEARCH_CORE
  (req : fairseq.CompletionRequest)
  (entry_pt : string) 
  (model_path : string) 
  (data_path : string)
  (fuel : ℕ := 25) :
  state_t BFSState tactic unit :=
  fairseq.fairseq_bfs_proof_search_core req entry_pt model_path data_path fuel

meta def main : io unit := do {
  args ← io.cmdline_args,
  decls_file ← args.nth_except 0 "decls_file",
  dest ← args.nth_except 1 "dest",
  max_tokens ← string.to_nat <$> args.nth_except 2 "max_tokens",
  (some temperature) ← (native.float.of_string <$> (lift_option $ args.nth 3)) | io.fail "must supply temperature",
  nbest ← string.to_nat <$> args.nth_except 4 "nbest",
  beam ← string.to_nat <$> args.nth_except 5 "beam",
  fuel ← string.to_nat <$> args.nth_except 6 "fuel",
  max_width ← string.to_nat <$> args.nth_except 7 "max_width",
  max_depth ← string.to_nat <$> args.nth_except 8 "max_depth",
  entry_pt ← lift_option $ args.nth 9 | io.fail "must supply entry point",
  model_path ← lift_option $ args.nth 10 | io.fail "must supply model path",
  data_path ← lift_option $ args.nth 11 | io.fail "must supply data path",
  tac_timeout ← string.to_nat <$> args.nth_except 12 "tac_timeout",
  global_timeout ← string.to_nat <$> args.nth_except 13 "global_timeout",

  let req : fairseq.CompletionRequest := {
    max_tokens := max_tokens,
    temperature := temperature,
    nbest := nbest,
    beam := beam,
    ..fairseq.default_partial_req
  },

  evaluation_harness_from_decls_file
    (SEARCH_CORE req entry_pt model_path data_path fuel)
      decls_file dest global_timeout $
        BFSState.of_current_state 0 max_width max_depth tac_timeout
}

end main
