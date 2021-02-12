import evaluation_step
import backends.bfs.openai

section main

local notation `ENGINE_ID` := ""
local notation `OPENAI_API_KEY` := ""

meta def SEARCH_CORE
  (req : openai.CompletionRequest)
  (engine_id : string := ENGINE_ID) (api_key : string := OPENAI_API_KEY) (fuel : ℕ := 25) :
  state_t BFSState tactic unit :=
  openai.openai_bfs_proof_search_core req engine_id api_key fuel

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

  let req := {
    max_tokens := max_tokens,
    temperature := temperature,
    top_p := top_p,
    n := n,
    best_of := best_of,
    ..openai.default_partial_req
  },

  evaluation_harness_from_decls_file (SEARCH_CORE req engine_id api_key fuel)
    decls_file dest global_timeout
     $ BFSState.of_current_state 0 max_width max_depth tac_timeout
}

end main
