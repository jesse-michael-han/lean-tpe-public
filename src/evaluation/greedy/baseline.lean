import evaluation_step
import backends.greedy.baseline

section main

-- use this version for testing using tidy_greedy_proof_search
meta def main : io unit := do {
  args ← io.cmdline_args,
  decls_file ← lift_option $ args.nth 0 | io.fail "must supply decls_file as first argument",
  dest ← lift_option $ args.nth 1 | io.fail "must supply dest as second argument",
  fuel ← string.to_nat <$> (lift_option $ args.nth 2) | io.fail "must supply fuel",
  tac_timeout ← string.to_nat <$> (lift_option $ args.nth 3) | io.fail "tac_timeout",
  global_timeout ← string.to_nat <$> (lift_option $ args.nth 4) | io.fail "global_timeout",
  
  evaluation_harness_from_decls_file (baseline.tidy_greedy_proof_search_core fuel) decls_file dest global_timeout (pure {tac_timeout := tac_timeout})
}

end main
