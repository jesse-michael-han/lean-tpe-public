import evaluation
import utils

namespace fairseq

section fairseq_api

meta structure CompletionRequest : Type :=
(prompt : string)
(max_tokens : int := 16)
(temperature : native.float := 1.0)
(nbest : int := 1)
(beam: int := 10)

meta def default_partial_req : CompletionRequest :=
{
  prompt := "",
  max_tokens := 6000,
  temperature := (1.0 : native.float),
  nbest := 1,
  beam := 10,
}


/-- this is responsible for validating parameters,
   e.g. ensuring floats are between 0 and 1 -/
meta instance : has_to_tactic_json CompletionRequest :=
let validate_max_tokens : int → bool := λ n, n ≤ 10000 in
let validate_float_frac : native.float → bool := λ k, 0 ≤ k ∧ k ≤ 1 in
let validate_and_return {α} (pred : α → bool) : α → tactic α := λ a, ((guard $ pred a) *> pure a <|> tactic.fail "VALIDATE_AND_RETURN FAILED") in
let validate_optional_and_return {α} (pred : α → bool) : option α → tactic (option α) := λ x, do {
  match x with
  | (some val) := some <$> validate_and_return pred val
  | none := pure none
  end
} in
let fn : CompletionRequest → tactic json := λ req, match req with
| ⟨prompt, max_tokens, temperature, nbest, beam⟩ := do
  max_tokens ← validate_and_return validate_max_tokens max_tokens,
  temperature ← validate_and_return validate_float_frac temperature,
  nbest ← validate_and_return (λ x, 0 ≤ x ∧ x ≤ (50 : int)) /- don't go overboard with the candidates -/ nbest,
  beam ← validate_and_return (λ x, 0 ≤ x ∧ x ≤ (50 : int)) /- don't go overboard with the candidates -/ beam,

  let pre_kvs : list (string × option json) := [
    ("prompt", json.of_string prompt),
    ("max_tokens", json.of_int max_tokens),
    ("temperature", json.of_float temperature),
    ("nbest", json.of_int nbest),
    ("beam", json.of_int beam)
  ],

  pure $ json.object $ pre_kvs.filter_map (λ ⟨k,mv⟩, prod.mk k <$> mv)
end
in ⟨fn⟩

meta def ENTRY_PT : string := "/Users/Yuhuai/Documents/research/scatter_transformer_fairseq/fairseq_cli/query.py"
meta def MODEL_PATH : string := "/Users/Yuhuai/Documents/research/scatter_transformer_fairseq/lean_multigoal_checkpoints/checkpoint_best.pt"
meta def DATA_PATH : string := "/Users/Yuhuai/Documents/research/scatter_transformer_fairseq/datasets/LeanMultiGoalStepSPBPE4000Bin"

meta def CompletionRequest.to_cmd (entry_pt: string) (model_path : string) (data_path : string)  : CompletionRequest → io (io.process.spawn_args)
| req@⟨prompt, max_tokens, temperature, nbest, beam⟩ := do
serialized_req ← io.run_tactic' $ has_to_tactic_json.to_tactic_json req,
pure {
  cmd := "python",
  args := [
      entry_pt
      , data_path
      , "--path"
      , model_path
      , "--sentencepiece-model"
      , data_path ++ "/model_4000_bpe.model"
      , "--json-msg"
      , json.unparse serialized_req
    ]
}

meta def serialize_ts
  (req : CompletionRequest)
  : tactic_state → tactic CompletionRequest := λ ts, do {
  ts_str ← postprocess_tactic_state ts, -- this function is responsible for replacing newlines with tabs and removing the "k goals" line
  let prompt : string :=
  ts_str,
  eval_trace format!"\n \n \n PROMPT: {prompt} \n \n \n ",
  pure {
    prompt := prompt,
    ..req}
}

meta def fairseq_api (entry_pt : string) (model_path : string) (data_path : string) : ModelAPI CompletionRequest :=

let get_predictions (response_msg : json) : option json :=
(lift_option $ do
    { (json.array choices) ← response_msg.lookup "choices" | none,
      /- `choices` is a list of {text: ..., index: ..., logprobs: ..., finish_reason: ...}-/
      texts ← choices.mmap (λ choice, choice.lookup "text"),
      pure texts
  }) in

let fn : CompletionRequest → io json := λ req, do {
  proc_cmds ← req.to_cmd entry_pt model_path data_path,
  response_raw ← io.cmd proc_cmds,
  io.put_str_ln' format!"RAW RESPONSE: {response_raw}",
  response_msg ← (lift_option $ json.parse response_raw) | io.fail' format!"[fairseq_api] JSON PARSE FAILED {response_raw}",
  (do predictions ← lift_option (get_predictions response_msg) | io.fail' format!"[fairseq_api] UNEXPECTED RESPONSE MSG: {response_msg}",
  io.put_str_ln' format!"PREDICTIONS: {predictions}",
  pure predictions) <|> pure (json.array $ [json.of_string $ format.to_string $ format!"ERROR {response_msg}"])
} in ⟨fn⟩

end fairseq_api

section fairseq_greedy_proof_search

meta def fairseq_greedy_proof_search_core
  (partial_req : fairseq.CompletionRequest)
  (entry_pt : string)
  (model_path : string)
  (data_path : string)
  (fuel := 5)
  : state_t GreedyProofSearchState tactic unit :=
greedy_proof_search_core
  (fairseq_api entry_pt model_path data_path)
    (fairseq.serialize_ts partial_req)
      (λ  msg n, run_best_beam_candidate (unwrap_lm_response $ some "[fairseq_greedy_proof_search_core]") msg n)
        (fuel)

meta def fairseq_greedy_proof_search
  (partial_req : fairseq.CompletionRequest)
  (entry_pt : string)
  (model_path : string)
  (data_path : string)
  (fuel := 5)
  (verbose := ff)
  : tactic unit :=
greedy_proof_search
  (fairseq_api entry_pt model_path data_path)
    (fairseq.serialize_ts partial_req)
      (λ  msg n, run_best_beam_candidate (unwrap_lm_response $ some "[fairseq_greedy_proof_search]") msg n)
        (fuel)
          (verbose)

end fairseq_greedy_proof_search

section test

-- example : true :=
-- begin
--   trythis "asdf",
--   sorry -- try using fairseq_greedy_proof_search here
-- end

-- example : true :=
-- begin
--   fairseq_greedy_proof_search {temperature :=1.0, nbest:=1, beam:=10, ..fairseq_api.default_partial_req}
--     fairseq_api.ENTRY_PT
--       fairseq_api.MODEL_PATH
--         fairseq_api.DATA_PATH,
-- end

-- open nat
-- example (n : ℕ) (m : ℕ) : nat.succ (n + m) = (nat.succ n + m) :=
-- begin
--   -- fairseq_greedy_proof_search {temperature :=0.7, nbest:=10, beam:=10, ..fairseq_api.default_partial_req}
--   --   fairseq_api.ENTRY_PT
--   --     fairseq_api.MODEL_PATH
--   --       fairseq_api.DATA_PATH,
-- end

-- #eval fairseq_api.CompletionRequest.to_cmd  {prompt := "true", nbest := 10, ..fairseq_api.default_partial_req} >>= io.cmd >>=io.put_str_ln
-- #eval fairseq_api.CompletionRequest.to_cmd  fairseq_api.default_partial_req >>= io.cmd >>= io.put_str_ln
-- #eval io.cmd {cmd:="echo", args:=["hello"]} >>= io.put_str_ln
-- #eval fairseq_api.serialize_ts fairseq_api.default_partial_req
end test

end fairseq
