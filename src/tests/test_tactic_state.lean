import ..evaluation
import utils
import ..tactic_state
import meta.expr
import all
import linear_algebra.tensor_algebra

meta def json.load (path : string) : tactic json := do {
  msg ← tactic.unsafe_run_io $ do {
    f ← io.mk_file_handle path io.mode.read,
    buffer.to_string <$> io.fs.read_to_end f
  },
  tactic.trace format!"[json.load] MESSAGE: {msg}",
  json.parse msg
}

section hom_ext'
meta def tactic.interactive.trace_tactic_state_data (f : string) : tactic unit :=
  do { msg ← (format.to_string ∘ format.flatten ∘ has_to_format.to_format) <$>
         (tactic_state_data.get >>= has_to_tactic_json.to_tactic_json),
       dest_handle ← tactic.unsafe_run_io $ io.mk_file_handle f io.mode.write,
       tactic.unsafe_run_io $ io.fs.put_str_ln dest_handle msg 
  }

meta def test_tactic_state (msg₀ : option json) (tac : tactic unit) : tactic unit := do {
  (some msg) ← (do
    if msg₀.is_some then do {msg ← msg₀, pure (some msg) } else 
      some <$> json.load "TEST_JSON.json" ),

  tactic.trace format!"MSG LENGTH {(json.unparse msg).length}",
  tactic.trace "REBUILDING TSD",
  tsd ← (has_from_json.from_json : json → tactic tactic_state_data) msg,
  tactic.trace "REBUILT TSD",
  rebuild_tactic_state tsd,
  env ← tactic.get_env,
  ts ← tactic.read,
  ctx ← tactic.local_context,
  tactic.trace format!"LOCAL CONTEXT: {ctx.map expr.to_raw_fmt}",
  result ← run_tac_with_tactic_state (tac *> pure ()) ts,
  tactic.trace "EVALUATION RESULT: " *> tactic.trace result,
  tactic.trace "OK"
}

set_option formatter.hide_full_terms false
set_option pp.implicit true
-- theorem t2 {p q r : Prop} (h₁ : p) (h₂ : q) : (p ∧ q) ∨ r :=
-- begin
--   apply or.inl,
--   trace_tactic_state_data "TEST_JSON.json",
--   -- do { tsd_msg ← tactic_state_data.get >>= has_to_tactic_json.to_tactic_json, test_tactic_state tsd_msg `[apply and.intro] },
--   do { msg ← (format.to_string ∘ format.flatten ∘ has_to_format.to_format) <$>
--          (tactic_state_data.get >>= has_to_tactic_json.to_tactic_json),
--        dest_handle ← tactic.unsafe_run_io $ io.mk_file_handle "TEST_JSON.json" io.mode.write,
--        tactic.unsafe_run_io $ io.fs.put_str_ln dest_handle msg
--   },
--   recover, sorry
--   -- apply and.intro, from ‹_›, from ‹_›
-- end

namespace tensor_algebra
variables (R : Type*) [comm_semiring R]
variables (M : Type*) [add_comm_monoid M] [semimodule R M]

-- @[ext]
-- theorem hom_ext' {A : Type*} [semiring A] [algebra R A] {f g : tensor_algebra R M →ₐ[R] A}
--   (w : f.to_linear_map.comp (ι R) = g.to_linear_map.comp (ι R)) : f = g :=
-- begin
--   rw [←lift_symm_apply, ←lift_symm_apply] at w,
--   do { msg ← (format.to_string ∘ format.flatten ∘ has_to_format.to_format) <$>
--          (tactic_state_data.get >>= has_to_tactic_json.to_tactic_json),
--        dest_handle ← tactic.unsafe_run_io $ io.mk_file_handle "TEST_JSON.json" io.mode.write,
--        tactic.unsafe_run_io $ io.fs.put_str_ln dest_handle msg
--   },
--   exact (lift R).symm.injective w,
-- end
-- #check has_from_json_name_aux

-- run_cmd do {msg ← json.load "TEST_JSON.json", tactic.trace msg, tactic.trace "HELLO", pure ()}


-- run_cmd test_tactic_state none `[apply and.intro] -- we have liftoff

setup_tactic_parser
-- #check lean.parser_state
-- run_cmd do {
--   ps ← lean.parser.mk_parser_state,
--   tactic.trace ps.cur_pos,
--   -- result ← (lean.parser.run' (texpr) " and.intro "),
--   result ← (lean.parser.run' (lean.parser.itactic) " { pure () }"),
--   -- let x := result.val,
--   -- x,
--   tactic.trace "HELLO"
-- }


end tensor_algebra
end hom_ext'
