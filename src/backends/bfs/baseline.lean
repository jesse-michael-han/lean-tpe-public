import tactic.tidy

import evaluation

namespace baseline

section tidy_proof_search

meta def tidy_default_tactics : list string := [
     "refl"
  ,  "exact dec_trivial"
  ,  "assumption"
  ,  "tactic.intros1"
  ,  "tactic.auto_cases"
  ,  "apply_auto_param"
  ,  "dsimp at *"
  ,  "simp at *"
  ,  "ext1"
  ,  "fsplit"
  ,  "injections_and_clear"
  ,  "solve_by_elim"
  ,  "norm_cast"
]

@[inline]
meta def tidy_default_tactics_json : json :=
json.array $ json.of_string <$> tidy_default_tactics

@[inline]
meta def tidy_default_tactics_scores : json :=
json.array $ json.of_float <$> list.repeat (0.0 : native.float) tidy_default_tactics.length

meta def tidy_api : ModelAPI := -- simulates logic of tidy, baseline (deterministic) model
let fn : json → io json := λ msg, do {
  pure $ json.array $ [tidy_default_tactics_json, tidy_default_tactics_scores]
} in ⟨fn⟩

-- TODO(jesse): pass and set max_width
meta def tidy_bfs_proof_search_core
   (fuel : ℕ := 1000)
   (verbose := ff)
   : state_t BFSState tactic unit :=
bfs_core
  tidy_api
    (λ _, pure json.null)
      (λ msg n, run_all_beam_candidates (unwrap_lm_response_logprobs $ some "[tidy_bfs_proof_search]") msg n)
        fuel

meta def tidy_bfs_proof_search
  (fuel : ℕ := 1000)
  (verbose := ff)
  (max_width := 25)
  (max_depth := 50)
  : tactic unit :=
  bfs tidy_api (λ _, pure json.null)
    (λ msg n, run_all_beam_candidates (unwrap_lm_response_logprobs $ (some "[tidy_bfs_proof_search]")) msg n)
      fuel verbose max_width max_depth

end tidy_proof_search

section playground

-- example : true :=
-- begin
--   tidy_bfs_proof_search 5 tt,
-- end

-- open nat
-- universe u
-- example : ∀ {α : Type u} {s₁ s₂ t₁ t₂ : list α},
--   s₁ ++ t₁ = s₂ ++ t₂ → s₁.length = s₂.length → s₁ = s₂ ∧ t₁ = t₂ :=
-- begin
--   intros, -- tidy_bfs_proof_search
-- end
-- open nat

-- example {p q r : Prop} (h₁ : p) (h₂ : q) : p ∧ q :=
-- begin
--   tidy_bfs_proof_search 3 tt
-- end
-- run_cmd do {set_show_eval_trace tt *> do env ← tactic.get_env, tactic.set_env_core env}

-- example {p q r : Prop} (h₁ : p) (h₂ : q) : p ∧ q :=
-- begin
--   tidy_bfs_proof_search 2 ff -- should only try one iteration before halting

end playground

end baseline
