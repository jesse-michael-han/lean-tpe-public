import .util

meta def unwrap_lm_response (ident : option string) : json → tactic (list string)
| (json.array $ tactic_strings) := do
    result ← tactic_strings.mmap $ lift_option ∘ json.get_string,
    pure result
| exc := tactic.fail format!"{ident.get_or_else \"[unwrap_lm_response.anonymous]\"} run_best_beam_candidate UNEXPECTED: {exc}"

meta def json_float_array_sum : json → option json
| (json.array xs) := json.of_float <$> xs.mfoldr (λ msg acc, match msg with
  | (json.of_float val) := pure $ acc + val
  | (json.of_int val) := pure $ acc + native.float.of_int val
  | exc := none
  end) (0.0 : native.float)
| exc := none

-- WARNING(jesse, January 14 2021, 10:32 AM): instead of failing like `unwrap_lm_response`, this return an empty list when seeing an unexpected message
meta def unwrap_lm_response_logprobs (ident : option string) : json → tactic (list $ string × native.float)
| (json.array $ [(json.array predictions), (json.array scores)]) := do {
  decoded_strings ← predictions.mmap $ lift_option ∘ json.get_string,
  decoded_scores ← scores.mmap $ lift_option ∘ json.get_float,
  pure $ list.zip decoded_strings decoded_scores
}
| exc := tactic.trace format!"{ident.get_or_else \"[unwrap_lm_response_logprobs.anonymous]\"} run_best_beam_candidate UNEXPECTED: {exc}" *> pure []

section json

-- for debugging

meta def json.compare : Π (x y : json), bool
| (json.of_string s) (json.of_string s') := s = s'
| (json.of_int k) (json.of_int k') := k = k'
| (json.of_float x) (json.of_float x') := x = x' -- might have to make this tt
| (json.of_bool b) (json.of_bool b') := b = b'
| (json.null) (json.null) := tt
| (json.object kvs) (json.object kvs') := (list.zip kvs kvs').foldr
  (λ ⟨⟨k₁, v₁⟩, ⟨k₂, v₂⟩⟩ acc,
  json.compare k₁ k₂ && json.compare v₁ v₂ && acc) tt
| (json.array args) (json.array args') := (list.zip args args').foldr
  (λ ⟨j₁, j₂⟩ acc, acc && json.compare j₁ j₂) tt
| _ _ := ff

meta def json.to_raw_fmt : json → format
| (json.of_string s) := format!"(json.of_string \"{s}\")"
| (json.of_int k) := format!"(json.of_int {k})"
| (json.of_float x) := format!"(json.of_float {x})"
| (json.of_bool b) := format!"(json.of_bool {b})"
| (json.null) := "(json.null)"
| (json.object kvs) := let f : string × json → format :=
  (λ ⟨k,v⟩, json.to_raw_fmt k ++ " : " ++ json.to_raw_fmt v) in
   format!"(json.object " ++ format.join_using " " (f <$> kvs) ++ ")"
| (json.array args) := "(json.array " ++ format.join_using " " (json.to_raw_fmt <$> args) ++ ")"

end json

section derive_has_json
section has_to_tactic_json_name
open name

-- meta def has_to_tactic_json_name_aux : name → json
-- | anonymous := json.object $ [("constr", json.of_string "name.anonymous"), ("args", json.array [])]
-- | (mk_string str nm) := json.object $ [("constr", json.of_string "name.mk_string"),
--     ("args", json.array [json.of_string str, has_to_tactic_json_name_aux nm])]
-- | (mk_numeral u nm) := json.object $ [("constr", json.of_string "name.mk_numeral"),
--     ("args", json.array [json.of_int (int.of_nat ∘ unsigned.to_nat $ u), has_to_tactic_json_name_aux nm])]

meta def has_to_tactic_json_name_aux : name → json
| anonymous := json.array ∘ pure $ json.of_string "name.anonymous"
| (mk_string str nm) := json.array $
  [json.of_string "name.mk_string", json.of_string str, has_to_tactic_json_name_aux nm]
| (mk_numeral u nm) := json.array $
  [json.of_string "name.mk_numeral", json.of_int (int.of_nat u.to_nat), has_to_tactic_json_name_aux nm]

 -- json.object $ [("constr", json.of_string "name.mk_numeral"),
 --    ("args", json.array [json.of_int (int.of_nat ∘ unsigned.to_nat $ u), has_to_tactic_json_name_aux nm])]

meta instance : has_to_tactic_json name :=
⟨pure ∘ has_to_tactic_json_name_aux⟩

end has_to_tactic_json_name

section has_from_json_name

-- meta def has_from_json_name_aux : json → tactic name
-- | arg@(json.object [("constr", json.of_string c), ("args", json.array args)]) := do {
--   tactic.trace format!"GOT MATCH: {arg}",
--   match c with
--   | "name.anonymous" := pure name.anonymous
--   | "name.mk_string" := do {
--     (str, nm_json) ← (do {
--       [json.of_string str, nm_json] ← pure args,
--       pure (str, nm_json)
--     } <|> tactic.fail
--             format!"[has_from_json_name_aux.inner_match_1.mk_string] unexpected: {args}"),
--     name.mk_string str <$> has_from_json_name_aux nm_json
--   }
--   | "name.mk_numeral" := do {
--     (u, nm_json) ← (do {
--       [json.of_int u, nm_json] ← pure args,
--       pure (u, nm_json)
--     } <|> tactic.fail
--             format!"[has_from_json_name_aux.inner_match_1.mk_numeral] unexpected: {args}"),
--     name.mk_numeral (unsigned.of_nat ∘ int.to_nat $ u) <$> has_from_json_name_aux nm_json
--   }
--   | exc := tactic.fail format!"[has_from_json_name_aux.inner_match_1] unexpected: {exc}"
--   end
-- }
-- | exc := tactic.fail format!"[has_from_json_name_aux] unexpected: {exc}"

meta def has_from_json_name_aux : json → tactic name
| arg@(json.array (c::args)) := do {
  -- tactic.trace format!"GOT MATCH: {arg}",
  match c with
  | "name.anonymous" := pure name.anonymous
  | "name.mk_string" := do {
    (str, nm_json) ← (do {
      [json.of_string str, nm_json] ← pure args,
      pure (str, nm_json)
    } <|> tactic.fail
            format!"[has_from_json_name_aux.inner_match_1.mk_string] unexpected: {args}"),
    name.mk_string str <$> has_from_json_name_aux nm_json
  }
  | "name.mk_numeral" := do {
    (u, nm_json) ← (do {
      [json.of_int u, nm_json] ← pure args,
      pure (u, nm_json)
    } <|> tactic.fail
            format!"[has_from_json_name_aux.inner_match_1.mk_numeral] unexpected: {args}"),
    name.mk_numeral (unsigned.of_nat ∘ int.to_nat $ u) <$> has_from_json_name_aux nm_json
  }
  | exc := tactic.fail format!"[has_from_json_name_aux.inner_match_1] unexpected: {exc}"
  end
}
| exc := tactic.fail format!"[has_from_json_name_aux] unexpected: {exc}"


meta instance : has_from_json name :=
⟨has_from_json_name_aux⟩

end has_from_json_name

open tactic
namespace tactic
namespace interactive

meta def mk_to_tactic_json (type : name) : tactic unit := do {
  ls ← local_context,
  (x::_) ← tactic.intro_lst [`arg],
  et ← infer_type x,
  xs ← tactic.induction x,
  xs.mmap' $ λ ⟨c, args, _⟩, do
    (args', rec_call) ← args.mpartition $ λ e, do {e' ← tactic.to_expr ``(tactic json), bnot <$> e'.occurs <$> tactic.infer_type e},
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
      _inst ← mk_app ``has_to_tactic_json [a_tp] >>= mk_instance,
      tactic.to_expr ``(@has_to_tactic_json.to_tactic_json _ (%%_inst) %%a))
    },
    args''' ← prod.fst <$> (fn args'').run rec_call,


    c ← tactic.resolve_constant c,
    refine ``((λ (ys : list $ tactic json),
      (λ x, json.array [has_to_tactic_json_name_aux %%c,
        json.array x]) <$>  ys.mmap id) _), -- lol
    args'''.mmap (λ e, refine ``(list.cons %%e _)),
    tactic.to_expr ``(([] : list (tactic json))) >>= tactic.exact
}

meta def derive_has_to_tactic_json (pre : option name) : tactic unit := do {
  vs ← local_context,
  `(has_to_tactic_json %%f) ← target,
  env ← get_env,
  let n := f.get_app_fn.const_name,
  d ← get_decl n,
  refine ``( { to_tactic_json := _ } ),
  tgt ← target,
  extract_def (with_prefix pre n <.> "to_tactic_json") ff $ mk_to_tactic_json n
}

meta def has_to_tactic_json_derive_handler' (nspace : option name := none) : derive_handler :=
higher_order_derive_handler ``has_to_tactic_json (derive_has_to_tactic_json nspace) [] nspace

@[derive_handler]
meta def has_to_tactic_json_derive_handler : derive_handler :=
guard_class ``has_to_tactic_json has_to_tactic_json_derive_handler'

end interactive
end tactic
end derive_has_json

section derive_from_json
open tactic
namespace tactic

namespace interactive

meta def get_constr_and_args (arg : json) : option (string × list json) :=
match arg with
| (json.array [json.of_string c, json.array args]) := pure (c, args)
| _ := none
end

-- meta def json_to_expr : Π (arg : json), tactic expr
-- | (json.object [("constr", nm_json), ("args", json.array args)]) := do {
--   -- let c_nm := hacky_name_from_string c,
--   c_nm ← (json_to_expr nm_json) >>= eval_expr name,
--   constr ← mk_const c_nm,
--   if args.length = 0 then do {
--   tp ← tactic.infer_type constr,
--   e_id ← to_expr ``(@id %%tp),
--   pure $ e_id.mk_app [constr] -- ???????????????
--   }
--   else do
--   constr.mk_app <$> (args.mmap json_to_expr)
-- }
-- | arg@(json.of_int k) := do { -- WARNING: this is a hack for now
--   pure `(int.to_nat k)
-- }
-- | exc@(json.array $ x@(((json.of_string c))::rest)) := if ("name" < c) then do nm ← has_from_json_name_aux x, pure $ (by apply_instance : has_reflect name) nm else tactic.fail format!"[json_to_expr.name] unexpected: {exc}"
-- -- | arg@(json.of_bool b) := do { -- WARNING: this is a hack for now
-- --   pure `(tt)
-- -- }
-- -- -- TODO(jesse): as needed, built special built-in logic to handle constants
-- -- -- TODO(jesse): use `resolve_name` on `nm` to get the `has_from_json` instance
-- -- -- then make a recursive call with `json_to_expr`
-- -- -- better yet, move this logic into `mk_from_json`

-- -- | arg@(json.object [("builtin", nm_json), ("val", val_json)]) := do {
-- --   env ← get_env,
-- --   nm ← (has_from_json_name_aux nm_json),
-- --   -- d ← env.get nm,
-- --   ty_reflected ← declaration.type <$> get_decl nm,

-- --   _inst ← to_expr ``(has_from_json %%nm) >>= mk_instance,
-- --   _inst2 ← to_expr ``(has_reflect %%nm) >>= mk_instance,
-- --   to_expr ``(has_from_json.from_json _ %%_inst %%arg)
-- --   -- to_expr ``(has_from_json.from_json %%_inst $ %%arg)
-- --   }
-- | exc := tactic.fail format!"[json_to_expr] unexpected: {exc}"

meta def json_to_expr : Π (arg : json), tactic unit
| (json.array $ [nm_json, json.array args]) := do {
  -- let c_nm := hacky_name_from_string c,
  c_nm ← (has_from_json_name_aux nm_json),
  constr ← mk_const c_nm,
  if args.length = 0 then do {
  tp ← tactic.infer_type constr,
  e_id ← to_expr ``(@id %%tp),
  tactic.apply (e_id.mk_app [constr]) *> pure ()
  }
  else do
  -- tactic.apply constr.mk_app <$> (args.mmap json_to_expr)
  tactic.apply constr,
  args.mmap' json_to_expr
}
| arg@(json.of_int k) := do { -- WARNING: this is a hack for now
  tactic.exact `(int.to_nat k)
}
| exc@(json.array $ x@(((json.of_string c))::rest)) := if ("name" < c) then do nm ← has_from_json_name_aux x, tactic.exact ((by apply_instance : has_reflect name) nm) else tactic.fail format!"[json_to_expr.name] unexpected: {exc}"
-- | arg@(json.of_bool b) := do { -- WARNING: this is a hack for now
--   pure `(tt)
-- }
-- -- TODO(jesse): as needed, built special built-in logic to handle constants
-- -- TODO(jesse): use `resolve_name` on `nm` to get the `has_from_json` instance
-- -- then make a recursive call with `json_to_expr`
-- -- better yet, move this logic into `mk_from_json`

-- | arg@(json.object [("builtin", nm_json), ("val", val_json)]) := do {
--   env ← get_env,
--   nm ← (has_from_json_name_aux nm_json),
--   -- d ← env.get nm,
--   ty_reflected ← declaration.type <$> get_decl nm,

--   _inst ← to_expr ``(has_from_json %%nm) >>= mk_instance,
--   _inst2 ← to_expr ``(has_reflect %%nm) >>= mk_instance,
--   to_expr ``(has_from_json.from_json _ %%_inst %%arg)
--   -- to_expr ``(has_from_json.from_json %%_inst $ %%arg)
--   }
| exc := tactic.fail format!"[json_to_expr] unexpected: {exc}"

/- TODO(jesse): probably a better, recursive/lazy way of doing this -/
meta def mk_from_json (pre : option name) : tactic unit := do {
  (x::_) ← tactic.intro_lst [`_arg],
  real_tgt@`(tactic %%tgt) ← target,
  y ← to_expr ``(json_to_expr %%x),
  -- let real_tgt := ``(reflected $ tactic %%tgt),

  -- _ ← to_expr ``(do %%y >>= eval_expr unit),
  -- tactic.read >>= λ ts, tactic.trace format!"TACTIC STATE AFTER EVAL: {ts}",
  -- pure ()
  -- tac ← eval_expr (tactic unit) y,
  -- tac
  -- `(tactic %%tgt) ← target,
  -- -- y ← to_expr ``(@id (tactic %%tgt)) >>= (λ f, pure $ f.mk_app [y]),
  -- -- tactic.trace format!"OK?: {y}",
  -- -- tactic.unfreeze_local_instances,

  -- OK, i think this approach was the right one since `eval_expr` has type exactly `tactic alpha`
  -- although maybe we could also do... pure?
  -- before this line, y is a reflection of `json_to_expr %%x`, which returns an expr which is supposed to be the target
  -- to force this to evaluate, we turns this entire thing into a thing of type tactic tgt,

  -- result ← to_expr ``(do %%y >>= eval_expr %%tgt),
  gs ← tactic.get_goals,

  -- m ← tactic.mk_meta_var real_tgt,
  -- let m' := `([m]).to_expr,

  -- result ← to_expr ``(do %%y >>= eval_expr %%tgt),
  -- this doesn't work because `y` is just `json_to_expr %%x`, which contains the open variable `%%x`
  -- result ← to_expr ``(do %%y) >>= eval_expr expr,

  result ← to_expr ``(do try trivial, m ← mk_mvar, set_goals [m], %%y, tactic.get_assignment m >>= eval_expr %%tgt),
  tactic.exact result *> done
  -- (eval_expr json x) >>= json_to_expr
}

-- #check get_constr_and_args
-- meta def mk_from_json (pre : option name) : tactic unit := do {
--   (x::_) ← tactic.intro_lst [`_arg],
--   let rec := `(pure () : tactic unit).to_expr,
--   f ← to_expr ``(match (get_constr_and_args %%x) with
--   | (some ⟨constr, args⟩) := %%rec
--   | none := tactic.fail "[mk_from_json] unexpected failure"
--   end),
--   tactic.fail "NYI"

-- -- (constr, args))
-- }

meta def derive_has_from_json (pre : option name) : tactic unit := do {
  vs ← local_context,
  `(has_from_json %%f) ← target,
  env ← get_env,
  let n := f.get_app_fn.const_name,
  d ← get_decl n,
  refine ``( { from_json := _ } ),
  tgt ← target,
  let extract_def_nm := (with_prefix pre n <.> "from_json"),
  extract_def extract_def_nm ff $ mk_from_json n
}

meta def has_from_json_derive_handler' (nspace : option name := none) : derive_handler :=
higher_order_derive_handler ``has_from_json (derive_has_from_json nspace) [] nspace

@[derive_handler]
meta def has_from_json_derive_handler : derive_handler :=
guard_class ``has_from_json has_from_json_derive_handler'

end interactive

end tactic

end derive_from_json

section test

-- @[derive [has_to_tactic_json, has_from_json]]

inductive my_nat' : Type
-- /- `(x : α)` -/
-- | foo : DUH'
-- /- `{x : α}` -/
| bar : my_nat'
| baz : my_nat' → my_nat'
-- /- `⦃x:α⦄` -/
-- | strict_implicit : DUH'
-- /- `[x : α]`. Should be inferred with typeclass resolution. -/
-- | inst_implicit : DUH'
-- /- Auxiliary internal attribute used to mark local constants representing recursive functions
--         in recursive equations and `match` statements. -/
-- | aux_decl : DUH'

attribute [derive has_to_tactic_json] my_nat'
attribute [derive has_from_json] my_nat'

attribute [derive [has_reflect]] my_nat
attribute [derive [has_to_tactic_json]] my_nat
attribute [derive [has_from_json]] my_nat

-- run_cmd (has_to_tactic_json.to_tactic_json (my_nat.zero) >>= (has_from_json.from_json : json → tactic my_nat) >>= tactic.trace)

-- meta instance : has_to_format my_nat :=
-- ⟨λ x, match x with | my_nat.zero := "my_nat.zero" | (my_nat.succ x) := "my_nat.succ " ++ (by exact _match x) end⟩

-- meta instance : has_from_json my_nat :=
-- ⟨λ k,
-- -- match k with
-- -- | (json.object $ [("constr", c), ("args", (json.array args))]) := do
-- --   nm ← has_from_json_name_aux c,
-- --   match nm with
-- --   | `my_nat.zero := pure $ my_nat.zero
-- --   | `my_nat.succ := my_nat.succ <$> begin dedup, exact _match args.head end
-- --   | exc := tactic.fail format!"unexpected constructor: {exc}"
-- --   end
-- -- | exc := tactic.fail format!"unexpected: {exc}"
-- -- end
-- by do {tactic.interactive.json_to_expr begin exact k end >>= tactic.exact}
-- ⟩

-- run_cmd (has_to_tactic_json.to_tactic_json (my_nat.succ $ my_nat.succ $ my_nat.zero) >>= tactic.trace)

-- run_cmd (has_to_tactic_json.to_tactic_json (my_nat.succ $ my_nat.succ $ my_nat.zero) >>= (has_from_json.from_json : json → tactic my_nat) >>= tactic.trace)

@[derive [has_to_tactic_json, has_from_json]]
inductive my_tree : Type
| leaf : my_nat → my_tree
| node : my_tree → my_tree → my_nat → my_tree

meta instance : has_to_format my_tree :=
⟨λ t, match t with
| (my_tree.leaf k) := format!"(leaf {k})"
| (my_tree.node t₁ t₂ k) := by exact format!"(node {_match t₁} {_match t₂} {k})"
end
⟩

def example_tree : my_tree := my_tree.node (my_tree.leaf my_nat.zero) (my_tree.leaf my_nat.zero) my_nat.zero

-- run_cmd (has_to_tactic_json.to_tactic_json example_tree >>= tactic.trace)
-- run_cmd (has_to_tactic_json.to_tactic_json example_tree >>= (has_from_json.from_json : json → tactic my_tree) >>= tactic.trace)
end test

section instances

/-
WARNING: derived `has_to_tactic_json` and `has_from_json` instances are not guaranteed to be inverses
this can be resolved by enforcing special logic in the `has_from_json` derive handler
-/

-- meta instance : has_to_tactic_json nat :=
-- ⟨has_to_tactic_json.to_tactic_json ∘ int.of_nat⟩

-- TODO(jesse): this is insane! write the special logic.
-- attribute [derive [has_to_tactic_json, has_from_json]] nat
meta instance : has_to_tactic_json nat :=
⟨pure ∘ json.of_int ∘ int.of_nat⟩

attribute [derive has_from_json] nat -- handled by special logic in `mk_from_json`

-- run_cmd (has_to_tactic_json.to_tactic_json 3 >>=
--  λ x, tactic.trace x *> ((has_from_json.from_json : json → tactic ℕ) x >>= tactic.trace))

-- meta instance : has_from_json nat :=
-- ⟨λ msg,
--   match msg with
--   | (json.of_int (int.of_nat k)) := pure k
--   | exc := tactic.fail format!"[has_from_json_nat] unexpected: {exc}"
--   end
-- ⟩

-- meta instance : has_to_tactic_json unsigned :=
-- ⟨has_to_tactic_json.to_tactic_json ∘ unsigned.to_nat⟩

meta instance : has_from_json unsigned :=
⟨λ msg,
  match msg with
  | (json.of_int (int.of_nat k)) := pure $ unsigned.of_nat k
  | exc := tactic.fail format!"[has_from_json_unsigned] unexpected: {exc}"
  end
⟩

meta instance has_to_tactic_json_list {α} [h : has_to_tactic_json α] : has_to_tactic_json (list α) :=
⟨by mk_to_tactic_json name.anonymous⟩
universe u
-- meta instance has_from_json_list {α : Type u} [reflected α] [h : has_from_json α] : has_from_json (list α) :=
-- ⟨by mk_from_json name.anonymous⟩
-- set_option formatter.hide_full_terms false
-- run_cmd (has_to_tactic_json.to_tactic_json [1,2] >>= λ x, tactic.trace x *> (has_from_json.from_json : json → tactic (list ℕ)) x)

meta instance has_from_json_list {α} [H : has_from_json α] : has_from_json (list α) :=
⟨λ msg, do
let ⟨fn⟩ := H in
match msg with
| (json.array $ [c, json.array args]) := do
  c_nm ← has_from_json_name_aux c,
  if c_nm = `list.nil then pure [] else
  if c_nm = `list.cons then (::) <$> fn args.head <*> do x ← (args.nth 1), (by exact _match x) else
  tactic.fail format!"[has_from_json_list] unexpected {msg}"
| exc := tactic.fail "[has_from_json_list] unexpected {exc}"
end
⟩

-- run_cmd (has_to_tactic_json.to_tactic_json 2 >>= (has_from_json.from_json : json → tactic ℕ) >>= tactic.trace)

-- run_cmd (has_to_tactic_json.to_tactic_json [1,2] >>= λ x, tactic.trace x *> (has_from_json_list.from_json : json → tactic (list ℕ)) x >>= tactic.trace)

meta instance has_to_tactic_json_option {α} [has_to_tactic_json α] : has_to_tactic_json (option α) :=
⟨by mk_to_tactic_json name.anonymous⟩

meta instance has_from_json_option {α} [H : has_from_json α] : has_from_json (option α) :=
⟨λ msg, do
let ⟨fn⟩ := H in
match msg with
| (json.array $ [c, json.array args]) := do
  c_nm ← has_from_json_name_aux c,
  if c_nm = `option.none then pure none else
  if c_nm = `option.some then option.some <$> fn args.head else
  tactic.fail format!"[has_from_json_option] unexpected {msg}"
| exc := tactic.fail "[has_from_json_option] unexpected {exc}"
end
⟩

-- run_cmd (has_to_tactic_json.to_tactic_json (some [1,2]) >>= λ x, tactic.trace x *> (has_from_json.from_json : json → tactic (option $ list ℕ)) x >>= tactic.trace) -- sweet

meta instance has_to_tactic_json_prod {α β} [has_to_tactic_json α] [has_to_tactic_json β] : has_to_tactic_json (α × β) :=
⟨by mk_to_tactic_json name.anonymous⟩

meta instance has_from_json_prod {α β : Type} [H : has_from_json α] [H' : has_from_json β] : has_from_json (prod α β) :=
⟨λ msg, do
let ⟨fn₁⟩ := H in
let ⟨fn₂⟩ := H' in
match msg with
| (json.array $ [c, json.array args]) := do
  (c_nm : name) ← has_from_json_name_aux c,
  if c_nm = `prod.mk then prod.mk <$> (args.nth 0 >>= fn₁) <*> (args.nth 1 >>= fn₂) else
  tactic.fail format!"[has_from_json_prod] unexpected {msg}"
| exc := tactic.fail "[has_from_json_prod] unexpected {exc}"
end
⟩

attribute [derive [has_to_format]] binder_info
attribute [derive [has_to_tactic_json, has_from_json, has_reflect]] level
attribute [derive [has_to_tactic_json, has_from_json]] binder_info

section expr'

meta inductive expr'
| var         : nat → expr'
| sort        : level → expr'
| const       : name → list level → expr'
| mvar        (unique : name)  (pretty : name)  (type : expr') : expr'
| local_const (unique : name) (pretty : name) (bi : binder_info) (type : expr') : expr'
| app         : expr' → expr' → expr'
| lam        (var_name : name) (bi : binder_info) (var_type : expr') (body : expr') : expr'
| pi         (var_name : name) (bi : binder_info) (var_type : expr') (body : expr') : expr'
| elet       (var_name : name) (type : expr') (assignment : expr') (body : expr') : expr'

attribute [derive [has_to_tactic_json, has_from_json, has_reflect]] expr'

-- #check (by apply_instance : has_from_json expr')

attribute [derive [has_to_format]] expr'

meta def expr'.to_expr : expr' → expr
| (expr'.var k) := expr.var k
| (expr'.sort l) := (expr.sort l)
| (expr'.const n ls) := (expr.const n ls)
| (expr'.mvar un pr ty) := (expr.mvar un pr $ expr'.to_expr ty)
| (expr'.local_const un pr bi ty) := (expr.local_const un pr bi $ expr'.to_expr ty)
| (expr'.app e₁ e₂) := (expr.app (expr'.to_expr e₁) (expr'.to_expr e₂))
| (expr'.lam nm bi tp body) := (expr.lam nm bi (expr'.to_expr tp) (expr'.to_expr body))
| (expr'.pi nm bi tp body) := (expr.pi nm bi (expr'.to_expr tp) (expr'.to_expr body))
| (expr'.elet nm tp assn body) := (expr.elet nm (expr'.to_expr tp) (expr'.to_expr assn) (expr'.to_expr body))

-- meta def expr'.to_expr : expr' → tactic expr := λ x, tactic.trace "CONVERTING TO EXPR" *> (x.to_expr)

meta def expr.to_expr' : expr → tactic expr'
| (expr.var k) := pure $ expr'.var k
| (expr.sort l) := pure $ (expr'.sort l)
| (expr.const n ls) := pure $ (expr'.const n ls)
| (expr.mvar un pr ty) := (expr'.mvar un pr <$> expr.to_expr' ty)
| (expr.local_const un pr bi ty) := (expr'.local_const un pr bi <$> expr.to_expr' ty)
| (expr.app e₁ e₂) := (expr'.app <$> (expr.to_expr' e₁) <*> (expr.to_expr' e₂))
| (expr.lam nm bi tp body) := (expr'.lam nm bi <$> (expr.to_expr' tp) <*> (expr.to_expr' body))
| (expr.pi nm bi tp body) := (expr'.pi nm bi <$> (expr.to_expr' tp) <*> (expr.to_expr' body))
| (expr.elet nm tp assn body) := (expr'.elet nm <$> (expr.to_expr' tp) <*> (expr.to_expr' assn) <*> (expr.to_expr' body))
| (expr.macro md es) := tactic.fail "[expr.to_expr'] no macros allowed!"

-- @[instance, priority 9000]
-- meta def has_from_json_expr' : has_from_json expr' :=
-- ⟨λ msg, match msg with
--   | (json.object $ [("constr", c), ("args", json.array args)]) := do
--     (c_nm : name) ← has_from_json_name_aux c,
--     -- tactic.trace "NAME MSG:" *> tactic.trace nm_msg,
--     if c_nm = `expr'.const then do [nm_msg, levels_msg] ← pure args, result ← expr'.const <$> has_from_json_name_aux nm_msg <*> @has_from_json.from_json (list level) (by apply_instance : has_from_json (list level)) levels_msg, tactic.trace format!"[has_from_json_expr'] RESULT: {result}", result.to_expr.to_expr' else
--     -- tactic.fail format!"[has_from_json_expr'] unexpected: {msg}"
--     @has_from_json.from_json _ expr'.has_from_json msg
--   | exc := tactic.fail format!"[has_from_json_expr'] OH NO unexpected: {exc}"
-- end
-- ⟩

end expr'

meta instance : has_to_tactic_json expr :=
⟨λ e, e.erase_annotations.to_expr' >>= has_to_tactic_json.to_tactic_json⟩

meta instance : has_from_json expr :=
⟨λ msg, expr'.to_expr <$> (has_from_json.from_json : json → tactic expr') msg⟩

-- run_cmd (has_to_tactic_json.to_tactic_json `(2).to_expr >>= tactic.trace) -- interesting

-- #check expr
-- open tactic.interactive

-- run_cmd (has_to_tactic_json.to_tactic_json `foo.bar.baz >>= (λ x, tactic.trace x *> ((has_from_json.from_json : json → tactic name) x >>= tactic.trace)))

-- private theorem foo {p q : Prop} : p → q → ∀ r, (p ∧ q) ∨ r :=
-- λ h₁ h₂ h₃, or.inl (and.intro ‹_› ‹_›)

meta instance : has_to_tactic_json bool := ⟨λ b, pure ↑b⟩
meta instance : has_from_json bool := ⟨λ msg, match msg with
| (json.of_bool b) := pure b
| exc := tactic.fail format!"[has_from_json_bool] unexpected: {exc}"
end
⟩

end instances
-- #check tactic.set_env_core
