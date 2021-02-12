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

meta def tidy_api : ModelAPI := -- simulates logic of tidy, baseline (deterministic) model
let fn : json → io json := λ msg, do {
  pure $ json.array $ json.of_string <$> tidy_default_tactics
} in ⟨fn⟩

meta def tidy_greedy_proof_search_core
   (fuel : ℕ := 1000)
   (verbose := ff)
   : state_t GreedyProofSearchState tactic unit :=
greedy_proof_search_core
  tidy_api
    (λ _, pure json.null)
      (λ msg n, run_best_beam_candidate (unwrap_lm_response $ some "[tidy_greedy_proof_search]") msg n)
        fuel

-- TODO(jesse): run against `tidy` test suite to confirm reproduction of `tidy` logic
meta def tidy_greedy_proof_search
   (fuel : ℕ := 1000)
   (verbose := ff)
   : tactic unit :=
greedy_proof_search
  tidy_api
    (λ _, pure json.null)
      (λ msg n, run_best_beam_candidate (unwrap_lm_response $ some "[tidy_greedy_proof_search]") msg n)
        fuel
          verbose

end tidy_proof_search

section playground

-- example : true :=
-- begin
--   tidy_greedy_proof_search 5 tt,
-- end

-- open nat
-- universe u
-- example : ∀ {α : Type u} {s₁ s₂ t₁ t₂ : list α},
--   s₁ ++ t₁ = s₂ ++ t₂ → s₁.length = s₂.length → s₁ = s₂ ∧ t₁ = t₂ :=
-- begin
--   intros, -- tidy_greedy_proof_search
-- end
-- open nat

-- example {p q r : Prop} (h₁ : p) (h₂ : q) : p ∧ q :=
-- begin
--   tidy_greedy_proof_search 3 tt
-- end
-- run_cmd do {set_show_eval_trace tt *> do env ← tactic.get_env, tactic.set_env_core env}

-- example {p q r : Prop} (h₁ : p) (h₂ : q) : p ∧ q :=
-- begin
--   tidy_greedy_proof_search 2 ff -- should only try one iteration before halting

end playground

end baseline
