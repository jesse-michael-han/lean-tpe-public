import evaluation_step
import backends.bfs.baseline
import utils

section main

open baseline

-- use this version for testing using tidy_greedy_proof_search
meta def main : io unit := do {
  args ← io.cmdline_args,
  decls_file ← args.nth_except 0 "decls_file",
  dest ← args.nth_except 1 "dest",
  fuel ← string.to_nat <$> args.nth_except 2 "fuel",
  max_width ← string.to_nat <$> args.nth_except 3 "max_width",
  max_depth ← string.to_nat <$> args.nth_except 4 "max_depth",
  tac_timeout ← string.to_nat <$> args.nth_except 5 "tac_timeout",
  global_timeout ← string.to_nat <$> args.nth_except 6 "global_timeout",
  evaluation_harness_from_decls_file
    (tidy_bfs_proof_search_core fuel)
      (decls_file)
        (dest) global_timeout $
          BFSState.of_current_state 0 max_width max_depth tac_timeout
}

end main
