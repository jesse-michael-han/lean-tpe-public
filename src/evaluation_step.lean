import system.io
import .utils.util
import .utils.json
import all
import .evaluation

meta def evaluation_harness_from_decls_file
  {search_state : Type}
  [has_to_tactic_json search_state]
  (search_core : state_t search_state tactic unit)
  (decls_file : string)
  (dest : string)
  (global_timeout : ℕ) -- seconds
  -- (register_task_id : search_state → string → search_state)
  [has_register_task_id search_state]
  [has_mark_global_timeout search_state]
  [has_register_decl_goal search_state]
  (init_state : tactic search_state)
  : io unit := do {
    nm_strs ← (io.mk_file_handle decls_file io.mode.read >>= λ f,
    (string.split (λ c, c = '\n') <$> buffer.to_string <$> io.fs.read_to_end f)),

  -- io.put_str_ln' format!"NM STRS: {nm_strs}",

  (nms : list (name × list name)) ← (nm_strs.filter $ λ nm_str, string.length nm_str > 0).mmap $ λ nm_str, do {
    ((io.run_tactic' ∘ parse_decl_nm_and_open_ns) $ nm_str)
  },

  io.put_str_ln' format!"[evaluation_harness_from_decls_file] GOT {nms.length} NAMES",

  -- io.put_str_ln' format!"NMS: {nms}",

  -- additionally filter out non-theorems
  -- TODO(jesse): do this offline in a separate Lean script
  let nms_unfiltered_len := nms.length,
  nms ← io.run_tactic' $ do {
    env ← tactic.get_env,
    nms.mfilter $ λ ⟨nm, _⟩, (do {
      decl ← env.get nm,
      pure decl.is_theorem
    } <|> pure ff)
  },

  io.put_str_ln' format! "[evaluation_harness_from_decls_file] WARNING: SKIPPING {nms_unfiltered_len - nms.length}",

  dest_handle ← io.mk_file_handle dest io.mode.write, -- TODO(jesse): write binary?
  let process_result : search_state → io unit := λ result, do {
    msg ← json.unparse <$> (io.run_tactic' $ has_to_tactic_json.to_tactic_json result),
    io.fs.put_str_ln_flush dest_handle msg
  },
  let process_result_trace : search_state → io unit := λ result, do {
    io.put_str_ln "[process_result_trace] UNPARSING MESSAGE",
    msg ← json.unparse <$> (io.run_tactic' $ has_to_tactic_json.to_tactic_json result),
    io.put_str_ln msg
  },

  -- io.put_str_ln' format!"NAMES: {nms}",
  io.put_str_ln "[evaluation_harness_from_decls_file] ENTERING run_proof_search_core",
  let trace_flag := tactic.is_trace_enabled_for `EVAL_TRACE,
  run_proof_search_core search_core nms process_result trace_flag global_timeout init_state
}


-- todo(jesse): hardcode OpenAI API options here
-- use `tidy_greedy_proof_search_core` for debugging
-- meta def SEARCH_CORE : state_t GreedyProofSearchState tactic unit :=
-- tidy_greedy_proof_search_core 15
