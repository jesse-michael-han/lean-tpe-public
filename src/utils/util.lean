import tactic
import .sexp
import control.traversable.derive
import data.string.basic
import meta.rb_map

infix `<e>`:100 := λ x y, tactic.to_expr y >>= x

section iterate_until

meta def iterate_until_aux
  {m} [monad m] [alternative m] {α}
  (tac :  m α) (stop : α → m bool) (fuel_exhausted_callback : m α)
  : Π (fuel : ℕ), m α
| 0 := do {result ← tac, mcond (stop result) (pure result) fuel_exhausted_callback}
| (n+1) := do { result ← tac, mcond (stop result) (pure result) (iterate_until_aux n)}

meta def iterate_until
  {m} [monad m] [alternative m] {α}
  (tac : m α) (stop : α → m bool) (fuel := 100000)
  (fuel_exhausted_callback : m α := alternative.failure)
  : m α
  :=
iterate_until_aux tac stop fuel_exhausted_callback fuel

end iterate_until

section interaction_monad

meta def interaction_monad.result.is_success {σ α} : interaction_monad.result σ α → bool := λ x,
match x with | (interaction_monad.result.success _ _) := tt | _ := ff end

end interaction_monad

section 

setup_tactic_parser

meta def parse_decl_nm_and_open_ns : string → tactic (name × list name) := λ inp,
flip lean.parser.run_with_input inp $ prod.mk <$> iterate_until ident (λ nm, pure ∘ bnot $ nm = name.anonymous) 100 <*> many ident

-- -- brilliant
-- #eval (["foo bar baz\n", "baz baz baz\n", "a b c d e\n"].mmap $ io.run_tactic' ∘ parse_decl_nm_and_open_ns) >>= λ x, io.put_str_ln' format!"{x}"

end 

section io
open interaction_monad interaction_monad.result
namespace io

meta def run_tactic' {α} (tac :tactic α) : io α := do {
  io.run_tactic $ do {
    result ← tactic.capture tac,
    match result with
    | (success val _) := pure val
    | (exception m_fmt pos _) := do {
      let fmt_msg := (m_fmt.get_or_else (λ _, format!"none")) (),
      let msg := format!"[io.run_tactic'] {pos}: tactic failed\n-------\n{fmt_msg}\n-------\n",
      tactic.trace msg,
      tactic.fail msg
    }
    end
  }
}

end io

end io

section list
parameter {α : Type}
variables [has_lt α] [decidable_rel (has_lt.lt : α → α → Prop)]

meta structure dedup_state : Type := 
(seen : native.rb_set α := native.mk_rb_set)
(result : list α := [])

meta def dedup_list_aux {m} [monad m] : list α → state_t dedup_state m unit
| [] := pure ()
| (x::xs) := do {
  σ ← get,
  when (not $ σ.seen.contains x) $
    modify $ λ σ, dedup_state.mk (σ.seen.insert x) (σ.result ++ [x]),
  dedup_list_aux xs
}

meta def list.dedup {m} [monad m] : list α → m (list α) := λ xs,
  dedup_state.result <$> prod.snd <$> state_t.run (dedup_list_aux xs) {}

/-- version of list.mfoldl with sane argument ordering -/
def list.iterM {m} [monad m] {α β} (xs : list α) (init : β) (body : β → α → m β) : m β :=
list.mfoldl body init xs

def list.iter {α β} (xs : list α) (init : β) (body : β → α → β) : β :=
list.foldl body init xs

end list

section list -- WARNING: hack

local notation `α` := string

meta structure dedup_state' : Type := 
(seen : native.rb_map α native.float := native.mk_rb_map)
(result : list (α) := [])

local notation `m` := tactic
meta def dedup_list_aux' : list (α × native.float) → state_t dedup_state' m unit
| [] := pure ()
| (x::xs) := do {
  σ ← get,
  if (σ.seen.contains x.1) then (do
    (some old_score) ← (pure $ σ.seen.find x.1) | state_t.lift tactic.failed,
    let new_seen := if x.2 > old_score then (σ.seen.erase x.1).insert x.1 x.2 else σ.seen,
    modify $ λ σ, dedup_state'.mk new_seen (σ.result),
    dedup_list_aux' xs)
    else do
    modify $ λ σ, dedup_state'.mk (σ.seen.insert x.1 x.2) (σ.result ++ [x.1]),
    dedup_list_aux' xs
}

meta def list.dedup' : list (α × native.float) → m (list $ α × native.float) := λ xs, do
  σ ← prod.snd <$> state_t.run (dedup_list_aux' xs) {},
  σ.result.mmap (λ x, do { prod.mk x <$> σ.seen.find x })

-- OK, seems to work
-- run_cmd list.dedup' [("foo", (1.0 : native.float)), ("foo", (2.0 : native.float))] >>= tactic.trace

end list

section name

namespace name

meta def is_aux : name → bool
| name.anonymous := ff
| (name.mk_string str nm) := (||) ((list.head str.to_list) = '_') (is_aux nm)
| (name.mk_numeral _ nm) := is_aux nm

end name

end name

section string

namespace string

def replace_char : string → char → char → string
| ⟨cs⟩ c₁ c₂ := ⟨cs.map (λ c, if c = c₁ then c₂ else c)⟩

end string

end string

section util

-- TODO(jesse): refactor when we expose mk_initial_parser_state
def hacky_name_from_string (nm_str : string) : name :=
let components : list string := nm_str.split (= '.') in
components.foldl (flip name.mk_string) name.anonymous

def drop_newlines (s : string) : string := ⟨s.data.filter (λ c, !(c = '\n'))⟩

namespace io

meta def fail' {α} (fmt : format) : io α := io.fail $ format.to_string fmt

meta def put_str_ln' : Π (fmt : format), io unit := io.put_str_ln ∘ format.to_string

namespace fs

def put_str_ln_flush (h : handle) (s : string) : io unit :=
put_str h s *> put_str h "\n" *> flush h

end fs

-- discards empty lines
meta def readlines (f : io.handle) : io (list string) := do {
  ls ← io.iterate [] (λ acc, do {
     do {
      r ← buffer.to_string <$> io.fs.get_line f,
      mcond (io.fs.is_eof f) (pure none) $ do
      pure ∘ pure $ if r.length = 0 then acc else acc ++ [r]
    }
  }),
  pure ls
}


end io

section list_nth_except

-- convenience function for command-line argument parsing
meta def list.nth_except {α} : list α → ℕ → string → io α := λ xs pos msg,
  match (xs.nth pos) with
  | (some result) := pure result
  | none := do {
    io.fail' format!"must supply {msg} as argument {pos}"
  }
  end

end list_nth_except

def unless {m} [monad m] (cond : bool) (body : m unit) :=
when (not cond) body

def unlessM {m} [monad m] (cond : m bool) (body : m unit) :=
mcond cond (pure ()) body

def whenM {m} [monad m] (cond : m bool) (body : m unit) :=
mcond cond body $ pure ()

def for_ {m α β} [monad m] (xs : list α) (body : α → m β) := list.mmap' body xs

def any : list bool -> bool := λ xs, xs.foldl (||) ff

def all : list bool → bool := λ xs, xs.foldl (&&) tt

inductive my_nat : Type
| zero : my_nat
| succ : my_nat → my_nat

-- probably in the stdlib somewhere
meta def lift_option {α} {m} [alternative m]: option α → m α :=
λo, match o with | (some x) := pure x | none := alternative.failure end

namespace tactic

meta def guard_sorry : expr → tactic unit := λ e, do {
  contains_sorry_flag ← e.mfold ff (λ e' _ acc, if acc then pure acc else pure $ bor acc $ e'.is_sorry.is_some),
  guard $ bnot contains_sorry_flag
}

meta def set_goal_to (goal : expr) : tactic unit :=
mk_meta_var goal >>= set_goals ∘ pure

meta def get_proof : Π (decl : declaration), tactic expr
| (declaration.thm _ _ _ value_thunk) := pure $ value_thunk.get
| _ := tactic.fail ""

meta def test_get_proof (nm : name) : tactic unit := do {
  e <- tactic.get_env,
  d <- e.get nm,
  get_proof d >>= tactic.trace
}

meta def get_proof_from_env (nm : name) : tactic expr := do {
  e ← get_env,
  d ← e.get nm,
  get_proof d
}

/-- Prints a 'Try this:' message. -/
meta def trythis : string → tactic unit
| s := tactic.trace (sformat!"Try this: {s}")

end tactic

-- meta instance has_to_json_list {α} [H : has_to_json α] : has_to_json (list α) :=
-- ⟨json.array ∘ list.map H.to_json⟩

-- meta instance has_to_tactic_json_list {α} [H : has_to_tactic_json α] : has_to_tactic_json (list α) :=
-- ⟨λ xs, json.array <$> (list.mmap H.to_tactic_json xs)⟩

-- -- TODO(jesse): questionable.
-- meta instance has_to_json_prod {α β} [H₁ : has_to_json α] [H₂ : has_to_json β] : has_to_json (α × β) :=
-- ⟨λ ⟨a,b⟩, by {tactic.unfreeze_local_instances, cases H₁ with f₁, cases H₂ with f₂, exact (json.array $ [f₁ a, f₂ b])}⟩

-- -- TODO(jesse): even more questionable.
-- meta instance has_to_tactic_json_prod {α β} [H₁ : has_to_tactic_json α] [H₂ : has_to_tactic_json β] : has_to_tactic_json (α × β) :=
-- ⟨λ ⟨a,b⟩, by {tactic.unfreeze_local_instances,
--              cases H₁ with f₁,
--              cases H₂ with f₂,
--              exact (json.array <$> ((list.cons) <$> (f₁ a) <*> ((::) <$> (f₂ b) <*> (pure []))))}⟩


-- open expr

-- meta def structured_tactic_json_of_expr : expr → tactic json := λ ex, do {
--   repr ← (format.to_string ∘ format.flatten) <$> tactic.pp ex,
--   match ex with
--   | e@(var k) := do {
--     pure $ json.object $
--     [("constructor", "var"), ("value", k), ("repr", repr)]}
--   | e@(sort l) := do {
--     pure $ json.object $
--     [("constructor", "sort"), ("level", to_string l), ("repr", repr)]} -- TODO(jesse): to_json instance for universe levels
--   | e@(const nm ls) := do {
--     pure $ json.object $
--     [("constructor", "const"), ("name", to_string nm),
--     ("levels", to_string ls), ("repr", repr)]}
--   | e@(mvar un pt tp) := do {
--     r ←  structured_tactic_json_of_expr tp,
--     pure $ json.object $
--     [("constructor", "mvar"), ("unique", to_string un), ("pretty", to_string pt),
--     ("type", r), ("repr", repr)]}
--   | e@(local_const un pt binder_info tp) := do {
--     r ←  structured_tactic_json_of_expr tp,
--     pure $ json.object $
--     [("constructor", "local_const"), ("unique", to_string un),
--     ("pretty", to_string pt), ("binder_info", has_repr.repr binder_info), ("type", r), ("repr", repr)]}
--   | e@(app e₁ e₂) := do {
--       r₁ ←  structured_tactic_json_of_expr e₁,
--       r₂ ←  structured_tactic_json_of_expr e₂,
--       pure $ json.object $
--     [("constructor", "app"), ("head", r₁),
--     ("body", r₁),  ("repr", repr)]}
--   | e@(lam var_name b_info var_type body) := do {
--     ⟨[b], e'⟩ ← tactic.open_n_lambdas e 1,
--     r₁ ← structured_tactic_json_of_expr var_type,
--     r₂ ← structured_tactic_json_of_expr e',
--     b_json ← structured_tactic_json_of_expr b,
--     pure $ json.object $
--     [("constructor", "lam"), ("var_name", to_string var_name),
--     ("binder", b_json),
--     ("binder_info", has_repr.repr b_info),
--     ("var_type", r₁), ("body", r₂), ("repr", repr)]}
--   | e@(pi var_name b_info var_type body) := do {
--     ⟨[b], e'⟩ ← tactic.open_n_pis e 1,
--     r₁ ← structured_tactic_json_of_expr var_type,
--     r₂ ← structured_tactic_json_of_expr e',
--     b_json ← structured_tactic_json_of_expr b,
--     pure $ json.object $
--     [("constructor", "pi"), ("var_name", to_string var_name),
--     ("binder", b_json),
--     ("binder_info", has_repr.repr b_info),
--     ("var_type", r₁), ("body", r₂), ("repr", repr)]}
--   | e@(elet var_name var_type var_assignment body) := do {
--     r₁ ← structured_tactic_json_of_expr var_type,
--     r₂ ← structured_tactic_json_of_expr var_assignment,
--     r₃ ← structured_tactic_json_of_expr body,
--     pure $ json.object $
--     [("constructor", "elet"), ("var_name", to_string var_name),
--     ("var_type", r₁), ("var_assignment", r₂), ("body", r₃), ("repr", repr)]}
--   | e@(macro md deps) := do {
--     deps_jsons ← deps.mmap structured_tactic_json_of_expr,
--     pure $ json.object $ [("constructor", "macro"), ("macro_def", (json.of_string ∘ name.to_string) $ expr.macro_def_name md),
--     ("deps", json.array $ deps_jsons), ("repr", repr)]}
--   end
-- }

-- meta instance : has_to_tactic_json expr := ⟨structured_tactic_json_of_expr⟩

-- namespace expr

-- meta def to_flattened_json : expr → tactic json := λ e,
--   json.of_string <$> ((format.to_string ∘ format.flatten) <$> has_to_tactic_format.to_tactic_format e)

-- meta def to_flattened_sexp_json : expr → tactic json := λ e,
--   json.of_string <$> (format.to_string ∘ has_to_format.to_format) <$> (sexp_of_expr none e)

-- end expr

end util

section unfold_macros

meta def expr.unfold_string_macros {elab} : expr elab → expr elab
| e := match e.is_string_macro with
       | (some a) := expr.unfold_string_macros a
       | none := e
       end

meta def expr.unfold_macros (e : expr) : tactic expr := do {
  -- env ← tactic.get_env,
  -- pure $ env.unfold_all_macros e
  pure $ e.unfold_string_macros.erase_annotations
}

end unfold_macros

section derive_has_to_format

meta def expr.join (tp : expr) : list expr → tactic expr := λ xs,
xs.foldr (λ e₁ acc, do {acc ← acc, tactic.to_expr ``(@list.cons %%tp %%e₁ %%acc)}) (tactic.to_expr ``(list.nil))

meta def format.join_using : format → list format → format := λ x xs,
format.join $ list.intercalate [x] (pure <$> xs)

meta def format.apply_constructor : format → list format → format := λ f fs,
match fs with
| [] := f
| fs := format.join_using " " [f, format.join ["(", format.join_using " " fs, ")"]]
end

open tactic
namespace tactic
namespace interactive

meta def mk_to_format (type : name) : tactic unit := do {
  ls ← local_context,
  (x::_) ← tactic.intro_lst [`arg],
  et ← infer_type x,
  xs ← tactic.induction x,
  xs.mmap' $ λ ⟨c, args, _⟩, do
    (args', rec_call) ← args.mpartition $ λ e, do {
      e' ← tactic.to_expr ``(format),
      bnot <$> e'.occurs <$> tactic.infer_type e
    },
    args'' ← args'.mmap (λ a, flip prod.mk a <$> (et.occurs <$> tactic.infer_type a)),
    let fn : list (bool × expr) → state_t (list expr) tactic (list expr) := λ args'', do {
      let pop : state_t (list expr) tactic (option expr) := do {
        xs ← get,
        match xs with
        | (a::as) := modify (λ _, as) *> pure (some a)
        | [] := pure none
        end
      },
      args''.mmap (λ ⟨b, a⟩, if b then do (some x) ← pop, pure x else state_t.lift $ do
      a_tp ← infer_type a,
      _inst ← mk_app ``has_to_format [a_tp] >>= mk_instance,
      tactic.to_expr ``(@has_to_format.to_format _ (%%_inst) %%a))
    },
    args''' ← prod.fst <$> (fn args'').run rec_call,
    c ← tactic.resolve_constant c,
    nm_tp ← to_expr ``(name),
    nm_fmt ← mk_app ``has_to_format [nm_tp] >>= mk_instance,
    fs ← expr.join `(format) args''',
    result ← to_expr ``(format.apply_constructor (@has_to_format.to_format %%nm_tp %%nm_fmt %%c) %%fs),
    tactic.exact result
}

meta def derive_has_to_format (pre : option name) : tactic unit := do {
  vs ← local_context,
  `(has_to_format %%f) ← target,
  env ← get_env,
  let n := f.get_app_fn.const_name,
  d ← get_decl n,
  refine ``( { to_format := _ } ),
  tgt ← target,
  extract_def (with_prefix pre n <.> "to_format") ff $ mk_to_format n
}

meta def has_to_format_derive_handler' (nspace : option name := none) : derive_handler :=
higher_order_derive_handler ``has_to_format (derive_has_to_format nspace) [] nspace

@[derive_handler]
meta def has_to_format_derive_handler : derive_handler :=
guard_class ``has_to_format has_to_format_derive_handler'

attribute [derive [has_to_format]] my_nat

end interactive
end tactic

end derive_has_to_format

section json

section has_to_json
universe u

meta class has_to_json (α : Type u) : Type (u+1) :=
(to_json : α → json)

meta class has_to_tactic_json (α : Type u) : Type (u+1) :=
(to_tactic_json : α → tactic json)

meta class has_from_json (α : Type u) : Type (u+1) :=
(from_json : json → tactic α)

end has_to_json

meta def list.lookup_prod {α β} : (list (α × β)) → (α → bool) → option β
| [] _ := none
| (⟨a,b⟩::xs) p := if p a then pure b else xs.lookup_prod p

meta def json.get_string : json → option string
| (json.of_string str) := pure str
| _ := none

meta def json.get_float : json → option native.float
| (json.of_float str) := pure str
| _ := none

meta def json.lookup : json → string → option json
| (json.object kvs) str := kvs.lookup_prod $ λ k, k = str
| _ _ := none

end json

section full_names

namespace tactic

meta def enable_full_names : tactic unit := do {
  set_bool_option `pp.full_names true
}

meta def with_full_names {α} (tac : tactic α) : tactic α :=
tactic.save_options $ enable_full_names *> tac

end tactic

meta def tactic_state.fully_qualified (ts : tactic_state) : tactic tactic_state := do {
  ts₀ ← tactic.read,
  tactic.write ts,
  result_ts ← tactic.with_full_names $ tactic.read,
  tactic.write ts₀,
  pure result_ts
}

meta def tactic_state.fully_qualified_string (ts : tactic_state) : tactic string := do {
  ts₀ ← tactic.read,
  tactic.write ts,
  result ← tactic.with_full_names $ (tactic.read >>= λ ts, pure ts.to_format.to_string),
  tactic.write ts₀,
  pure result
}

end full_names

-- TODO(jesse): typeclasses also for updating decl_name
section search_state_instances

class has_mark_global_timeout (α : Type) : Type :=
(mark_global_timeout : α → α)

class has_register_task_id (α : Type) : Type :=
(register_task_id : α → string → α)

class has_set_tac_timeout (α : Type) : Type :=
(set_tac_timeout : α → ℕ → α)

class has_get_tac_timeout (α : Type) : Type :=
(get_tac_timeout : α → ℕ)

class has_mark_fuel_exhausted (α : Type) : Type :=
(mark_fuel_exhausted : α → α)

class has_register_decl_goal (α : Type) : Type :=
(register_decl_goal : α → string → α)

end search_state_instances

section eval_trace

meta def EVAL_TRACE := tt

meta def set_show_eval_trace : bool → tactic unit := tactic.set_bool_option `evaltrace

-- meta def eval_trace {α} [has_to_tactic_format α] : α → tactic unit | a := do
--   st ← tactic.get_bool_option `evaltrace ff,
--   if st || EVAL_TRACE then tactic.trace a else pure ()

meta def eval_trace {α} [has_to_tactic_format α] : α → tactic unit | a := do {
  evaltrace_flag ← tactic.get_bool_option `evaltrace ff,
  -- let trace_flag := tactic.is_trace_enabled_for `EVAL_TRACE,
  let trace_flag := EVAL_TRACE,
  let cond := (trace_flag || evaltrace_flag),
  when cond (tactic.trace a)
}

end eval_trace

section set_env_at_decl

meta def get_env_at_decl (decl_nm : name) : tactic environment := do {
  env ← tactic.get_env,
  lean_file ← env.decl_olean decl_nm,
  pure $ environment.for_decl_of_imported_module lean_file decl_nm
}

meta def set_env_at_decl (decl_nm : name) : tactic unit := do {
    env ← get_env_at_decl decl_nm,
    eval_trace format!"[set_env_at_decl] GOT ENV AT DECL {decl_nm}",
    tactic.set_env_core env,
    eval_trace format!"[set_env_at_decl] SET ENV AT DECL {decl_nm}"
}

end set_env_at_decl
