import utils
import evaluation
import all
import basic.table
import system.io

section parse_nm

meta def parse_nm : string → tactic name := λ nm_str, do {
  flip lean.parser.run_with_input nm_str $ iterate_until lean.parser.ident (λ nm, pure ∘ bnot $ nm = name.anonymous) 100
}

end parse_nm

meta def unpack_tactic_strings : json → tactic (list string) := λ msg, match msg with
| (json.array $ msgs) := do {
    msgs.mmap $ λ msg, match msg with
    | (json.of_string x) := pure x
    | exc := tactic.fail format! "UNEXPECTED {exc}"
    end
  }
| exc := tactic.fail format! "UNEXPECTED {exc}"
end

meta def get_decl_name_and_tactics (msg : json) : tactic $ name × list string := do {
  decl_name_msg ← msg.lookup "task_id",
  decl_name_str ← match decl_name_msg with
    | (json.of_string x) := pure x
    | exc := tactic.fail format! "UNEXPECTED {exc}"
    end,
  decl_name ← parse_nm decl_name_str,
  tacs_msg ← msg.lookup "tactics",
  tac_strings ← unpack_tactic_strings tacs_msg,
  pure ⟨decl_name, tac_strings⟩
}

-- #eval do {
--   msg ← option.to_monad $ json.parse " { \"task_id\":\"and.comm\", \"tactics\":[\"intros\", \"refine ⟨_,_⟩; intro h; cases h; exact and.intro ‹_› ‹_›\"]}",
--   x@⟨nm, tacs⟩ ← io.run_tactic' (get_decl_name_and_tactics msg),
--   io.put_str_ln' format! "{x}"

-- }

example : ∀ {a b : Prop}, a ∧ b ↔ b ∧ a :=
begin
  intros, refine ⟨_,_⟩; intro h; cases h; exact and.intro ‹_› ‹_›
end

meta def example_msg : tactic json := json.parse
  " { \"task_id\":\"finset.filter_not\",
      \"tactics\":[
        \"intros a\",
        \"intros\",
        \"ext b\",
        \"by_cases p b; simp *\"
      ]
    }"

meta def buggy_example_msg : tactic json := json.parse $
  " { \"task_id\":\"mvqpf.cofix.bisim\",
      \"tactics\":[
        \"intros x y h\",
        \"rintros x₀ y₀ q₀ hr\",
        \"intros x y h\",
        \"induction x using fin2.elim0\"
      ]
    }"

meta def replay_proof (namespaces : list name := []) :
  (name × list string) → tactic expr := λ ⟨decl_name, tacs⟩, do {
  env₀ ← tactic.get_env,
  tsd ← get_tsd_at_decl decl_name,
  env ← get_env_at_decl decl_name,
  tactic.set_env_core env,
  rebuild_tactic_state tsd,
  [g] ← tactic.get_goals,
  goal ← tactic.infer_type g,
  tactic.trace format! "[replay_proof] TACTICS: {tacs}",
  for_ tacs $ λ tac_str, do {
    tac ← parse_itactic tac_str,
    tac
  },

  pf ← tactic.get_assignment g >>= tactic.instantiate_mvars,
  tactic.set_env_core env₀,
  tactic.done <|> tactic.fail format! "[replay_proof] ERROR: NOT DONE WITH {decl_name}",
  validate_proof pf,
  pure pf
}

-- this should pass all checks
-- run_cmd do {
--   msg ← example_msg,
--   get_decl_name_and_tactics msg >>= replay_proof
-- }

-- this should pass `done` check but fail validation
-- run_cmd do {
--   msg ← buggy_example_msg,
--   get_decl_name_and_tactics msg >>= replay_proof
-- }

meta def pf_term_size (pf : expr) : tactic ℕ := do {
  str ← (format.to_string ∘ format.flatten) <$> tactic.pp pf,
  pure str.length
}

meta def build_namespace_index (decls_file : string) : io $ dict name (list name) := do {
    nm_strs ← (io.mk_file_handle decls_file io.mode.read >>= λ f,
    (string.split (λ c, c = '\n') <$> buffer.to_string <$> io.fs.read_to_end f)),

  -- io.put_str_ln' format!"NM STRS: {nm_strs}",

  (nms : list (name × list name)) ← (nm_strs.filter $ λ nm_str, string.length nm_str > 0).mmap $ λ nm_str, do {
    ((io.run_tactic' ∘ parse_decl_nm_and_open_ns) $ nm_str)
  },

  io.put_str_ln' format!"[evaluation_harness_from_decls_file] GOT {nms.length} NAMES",

  -- io.put_str_ln' format!"NMS: {nms}",

  -- additionally filter out non-theorems
  -- TODO(): do this offline in a separate Lean script
  let nms_unfiltered_len := nms.length,
  nms ← io.run_tactic' $ do {
    env ← tactic.get_env,
    nms.mfilter $ λ ⟨nm, _⟩, (do {
      decl ← env.get nm,
      pure decl.is_theorem
    } <|> pure ff)
  },
  pure $ dict.of_list nms
}

meta def mk_shorter_proof_jsonline (old_size : ℕ) (new_size : ℕ)
  (decl_nm : name) (tacs : list string) : json := do {
  json.array $ [old_size, new_size, decl_nm.to_string, json.array $ json.of_string <$> tacs]
}

meta def main : io unit := do {
  args ← io.cmdline_args,
  jsons_file ← args.nth_except 0 "jsons_file",
  dest ← args.nth_except 1 "dest",
  ns_index_path ← args.nth_except 2 "ns_index",
  msg_strs ← io.mk_file_handle jsons_file io.mode.read >>= λ f,
    (string.split (λ c, c = '\n') <$> buffer.to_string <$> io.fs.read_to_end f),
  let msg_strs := msg_strs.filter (λ x, x.length > 0),
  msgs ← msg_strs.mmap (λ msg_str, lift_option $ json.parse msg_str),
  dest_handle ← io.mk_file_handle dest io.mode.write,
  ns_index ← build_namespace_index ns_index_path,
  for_ msgs $ λ msg, io.run_tactic' $ do {
    x@⟨decl_nm, tacs⟩ ← get_decl_name_and_tactics msg,
    if tacs.length = 0 then tactic.trace format! "SKIPPING {decl_nm}" else do
    tactic.trace format! "REPLAYING {decl_nm}",
    old_pf_term ← tactic.get_proof_from_env decl_nm,
    tactic.trace format! "PROCESSING DECL_NM {decl_nm}",
    env₀ ← tactic.get_env,
    tactic.try $ do {
      open_ns ← ns_index.get decl_nm,
      new_pf_term ← replay_proof open_ns x,
      tactic.set_env_core env₀,
      old_size ← pf_term_size old_pf_term,
      tactic.trace format! "OLD SIZE: {old_size}",
      new_size ← pf_term_size new_pf_term,
      tactic.trace format! "NEW SIZE: {new_size}",
      when (new_size < old_size) $ tactic.unsafe_run_io $ do {
        io.put_str_ln "FOUND SMALLER PROOF",
        io.fs.put_str_ln_flush dest_handle $
          json.unparse $ mk_shorter_proof_jsonline old_size new_size decl_nm tacs
      }},
    tactic.set_env_core env₀
  }
}
