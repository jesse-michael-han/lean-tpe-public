import ..tactic_state
import ..evaluation
import tactic.auto_cases
import linear_algebra.tensor_algebra
import data.pfun

section playground

-- TODO(jesse): WARNING: without conjugating by `get/set_env`,
-- this has mysterious side effects which cause future invocations to `run_evaluation` to fail
run_cmd do {
  env ← tactic.get_env,
  tsd ← get_tsd_at_decl `roption.mem_to_option,
  tactic.trace tsd,
  tactic.set_env_core env
}

end playground

section main

meta def main : io unit := io.run_tactic $ do {
  let decl_nm := `tensor_algebra.hom_ext,
  tsd ← get_tsd_at_decl decl_nm,
  let tactic_string := "intros, rw [←lift_symm_apply, ←lift_symm_apply] at w,",
  let inp : EvaluationInput := ⟨decl_nm, tsd, tactic_string, [`tensor_algebra]⟩,
  result ← run_evaluation inp,
  tactic.trace result
}

end main
