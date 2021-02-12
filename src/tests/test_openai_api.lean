import evaluation
import backends.greedy.openai

open openai

meta def main : io unit := do
  m_api_key ← io.env.get "OPENAI_API_KEY",
  match m_api_key with
  | none := io.fail "ENVIRONMENT VARIABLE $OPENAI_API_KEY NOT FOUND"
  | (some api_key) := do
  cmd_args ← dummy_cr.to_cmd "davinci" api_key,
  io.put_str_ln $ format.to_string format!"ARGS BEFORE QUERY: {cmd_args}",
  result ← io.cmd cmd_args,
  io.put_str_ln result
  end
