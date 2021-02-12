import evaluation_step
import backends.greedy.openai

section main

local notation `ENGINE_ID` := ""
local notation `OPENAI_API_KEY` := ""

meta def SEARCH_CORE
  (req : openai.CompletionRequest)
  (engine_id : string := ENGINE_ID) (api_key : string := OPENAI_API_KEY) (fuel : ℕ := 25) :
  state_t GreedyProofSearchState tactic unit :=
  openai.openai_greedy_proof_search_core req engine_id api_key fuel

meta def main : io unit := do {
  args ← io.cmdline_args,
  decls_file ← lift_option $ args.nth 0 | io.fail "must supply decls_file as first argument",
  dest ← lift_option $ args.nth 1 | io.fail "must supply dest as second argument",
  max_tokens ← string.to_nat <$> (lift_option $  args.nth 2) | io.fail "must supply max tokens",
  (some temperature) ← (native.float.of_string <$> (lift_option $ args.nth 3)) | io.fail "must supply temperature",
  (some top_p) ← (native.float.of_string <$> (lift_option $ args.nth 4)) | io.fail "must supply top_p",
  n ← string.to_nat <$> (lift_option $ args.nth 5) | io.fail "must supply n",
  best_of ← string.to_nat <$> (lift_option $ args.nth 6) | io.fail "must supply best_of",
  fuel ← string.to_nat <$> (lift_option $ args.nth 7) | io.fail "must supply fuel",
  engine_id ← lift_option $ args.nth 8 | io.fail "must supply engine id",
  api_key ← lift_option $ args.nth 9 | io.fail "must supply api key",
  tac_timeout ← string.to_nat <$> args.nth_except 10 "tac_timeout",
  global_timeout ← string.to_nat <$> args.nth_except 11 "global_timeout",

  let req := {
    max_tokens := max_tokens,
    temperature := temperature,
    top_p := top_p,
    n := n,
    best_of := best_of,
    ..openai.default_partial_req
  },

  evaluation_harness_from_decls_file (SEARCH_CORE req engine_id api_key fuel) decls_file dest global_timeout $ pure {tac_timeout := tac_timeout}
}

end main
