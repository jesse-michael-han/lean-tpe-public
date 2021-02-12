import system.io
import utils
-- import all -- uncomment as needed, depending on the `decls_file`
import ..evaluation

/-- checks that we can get and set the tactic_state_data from a list of files -/
meta def test_get_tsd
  (decls_file : string)
  : io unit := do {
    nm_strs ← (io.mk_file_handle decls_file io.mode.read >>= λ f,
    (string.split (λ c, c = '\n') <$> buffer.to_string <$> io.fs.read_to_end f)),

  -- io.put_str_ln' format!"NM STRS: {nm_strs}",

  (nms : list (name × list name)) ← (nm_strs.filter $ λ nm_str, string.length nm_str > 0).mmap $ λ nm_str, do {
    ((io.run_tactic' ∘ parse_decl_nm_and_open_ns) $ nm_str)
  },

  io.put_str_ln' format!"[evaluation_harness_from_decls_file] GOT {nms.length} NAMES",

  for_ nms (
    let body : (name × list name) → io unit := λ ⟨decl_nm, open_ns⟩, do {
      when (decl_nm.length > 0) $ do
      env₀ ← io.run_tactic' $ tactic.get_env,
      io.run_tactic' $ (do {
        tsd_result ← tactic.capture $ get_tsd_at_decl decl_nm,
        tsd ← match tsd_result with
        | (interaction_monad.result.success val state) := tactic.resume tsd_result *> pure val
        | exc@(interaction_monad.result.exception _ _ _) := tactic.trace format!"[test_get_tsd] SERIALIZATION FAILED ON {decl_nm} HELLO \n---{exc}\n---" *> tactic.fail exc
        end,

        rebuild_result ← tactic.capture (rebuild_tactic_state tsd),
        match rebuild_result with
        | (interaction_monad.result.success val state) := tactic.resume rebuild_result
        | exc := tactic.trace format!"[test_get_tsd] RECONSTRUCTION FAILED ON {decl_nm} GOODBYE \n---{exc}\n---" *> tactic.resume exc
        end,
        tactic.trace format!"REBUILT TSD FOR DECL: {decl_nm}"
      }) <|> pure (),
      io.run_tactic' $ tactic.set_env_core env₀
    } in
    body
  )
}

meta def main : io unit := do {
  args ← io.cmdline_args,
  decls_file ← lift_option $ args.nth 0 | io.fail "must supply decls_file as first argument",
  io.put_str_ln' format!"[test_get_tsd.main] ENTERING test_get_tsd {decls_file}",
  test_get_tsd decls_file
}
