import evaluation
import backends.bfs.openai

/-- A tactic that will ring up GPT to ask for help solving a goal.
Remember to set the `OPEN_AI_KEY` environment variable.
Eg:
```sh
# ~/.zshenv
export OPEN_AI_KEY="<PUT YOUR SECRET KEY IN HERE>"
```
you may need to relogin to update.

`n` is the number of iterations for the greedy search.
`temperature` is a float between 0 and 1, and controls how deterministic the predictions are.
-/

meta def try_lookup_key (env : environment) : tactic string := do {
  key_decl ← env.get `OPENAI_API_KEY,
  val ← tactic.eval_expr string key_decl.value,
  pure val
}

meta def get_openai_api_key : tactic string := do {
  env ← tactic.get_env,
  -- TODO(jesse): for some reason try_lookup_key fails to resolve the name
  (try_lookup_key env <|> (tactic.unsafe_run_io $ io.env.get "OPENAI_API_KEY") >>= lift_option) <|>
    tactic.fail "can't find a key at OPENAI_API_KEY"
}

meta def lookup_key : tactic string := do {
  env ← tactic.get_env,
  d ← env.get `OPEN_AI_KEY,
  tactic.eval_expr string d.value
}

namespace tactic
namespace interactive

setup_tactic_parser

/-
`n` is the number of parallel requests for the greedy search.
`depth` is the number of iterations to run the greedy search
`temperature` is a float between 0 and 1, and controls how
 deterministic the predictions are.
-/
meta structure GPTSuggestConfig : Type :=
(n : ℕ := 32)
(fuel : ℕ := 0)
(temp : native.float := 1.0)
(silent := ff)
(max_depth : ℕ := 50)
(max_width : ℕ := 10)

open openai

--- meta def gptf (cfg : GPTSuggestConfig := {}) : tactic unit :=
-- tactic.success_if_fail done *> do {
--   let ⟨n, fuel, temperature, silent⟩ := cfg,
--   let partial_req := { n := n, temperature := temperature, .. default_partial_req },
--   let engine_id := "formal-3b-lean-webmath-1230-v2-c4",
--   api_key ← get_openai_api_key,
--   ps ← prod.snd <$> state_t.run
--          (openai_greedy_proof_search_core partial_req engine_id api_key fuel) {},
--   when (not silent) $ do {
--     tactic.trace "Predictions\n",
--     ps.predictions.head.mmap' tactic.trythis,
--     tactic.trace "\nTactics:\n",
--     tactic.trythis $ string.intercalate ", " (ps.tactics)
--   }
-- }

meta def gptf_core (cfg : GPTSuggestConfig := {}) : tactic (list string × list string) := do {
tactic.success_if_fail done *> do {
  let ⟨n, fuel, temperature, silent, max_depth, max_width⟩ := cfg,
  let partial_req := { n := n, temperature := temperature, .. default_partial_req },
  -- let engine_id := "formal-3b-lean-webmath-1230-v2-c4",
  let engine_id := "formal-large-lean-0119-mix-v1-c4",
  api_key ← get_openai_api_key,
  init_state ← BFSState.of_current_state fuel max_width max_depth 3,
  ps ← prod.snd <$> state_t.run
         (openai_bfs_proof_search_core partial_req engine_id api_key fuel) init_state,
  -- two cases: either the proof has finished and `tactics` field is populated
  -- or proof is not finished and we have to inpsect the open nodes on the search queue
  let predictions := ps.predictions.head,
  if ps.tactics.length = 0 then prod.mk predictions <$> ps.nodes.mfold (λ acc node, pure $ list.append acc [string.intercalate "," node.tactics]) []
    else pure $ prod.mk predictions $ pure $ ",".intercalate ps.tactics
  }
}

meta def gptf (cfg : GPTSuggestConfig := {}) : tactic unit := do {
  ⟨predictions, tactics⟩ ← gptf_core cfg,    
  tactic.trace "\nPredictions:\n",
  predictions.mmap' tactic.trythis,
  tactic.trace "\nTactics:\n",
  tactics.mmap' tactic.trythis
}

private meta def gptf_string (cfg : GPTSuggestConfig := {}) : tactic string := do {
  ⟨_, tactics⟩ ← gptf_core cfg,
  match tactics with
  | (x::xs) := pure x
  | [] := tactic.fail "[gptf'] NO CANDIDATES FOUND"
  end
}

-- TODO(jesse): try running with low max_width, high max_depth, and relatively low fuel (25-50)
meta def neuroblast (fuel : ℕ := 50) : tactic unit := gptf {fuel := fuel, max_width := 5, max_depth := 25}

-- TODO(jesse): distribution of states induced by `tidy` is unfamiliar for the model
-- might get more gains by augmenting with synthetic data/RL
meta def neuroblast₂ (trace : parse $ optional (tk "?")) : tactic unit := do {
  let neuroblast_cfg : tidy.cfg := {trace_result := trace.is_some, tactics := 
  tidy.default_tactics ++ [gptf_string]},
  tactic.tidy.core neuroblast_cfg *> pure ()
}

end interactive
end tactic

-- `gpt` Hello World
example {α} (a : α) : a = a :=
begin
  refl
end

example : ∃ n : ℕ, 8 = 2*n :=
begin
  exact ⟨4, rfl⟩
end

example {P Q R : Prop} : P → (P → R) → R :=
begin
  intros h1 h2, exact h2 h1
end

example {p q r : Prop} (h₁ : p) (h₂ : q) : (p ∧ q) ∨ r :=
begin
  exact or.inl ⟨h₁, h₂⟩
end

example {P Q : Prop} : (¬ P) ∧ (¬ Q) → ¬ (P ∨ Q) :=
begin
  intro h, simp [h]
end

example {P Q R : Prop} : (P ∧ Q) → ((P → R) → ¬ (Q → ¬ R)) := 
begin
  rintros ⟨h₁, h₂⟩ hh, apply not_imp_of_and_not; intros; cc
  -- intros h1 h2, intros h3, cases h1 with p h1, apply h3 _ (h2 p), exact h1
end
