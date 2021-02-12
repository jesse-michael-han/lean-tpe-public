import tactic.basic

section sexp
universe u
inductive sexp (α : Type u) : Type u
| atom : α → sexp
| list : (list sexp) → sexp

meta def sexp_to_format {α : Type u} [has_to_format α] : sexp α → format
| (sexp.atom val) := has_to_format.to_format val
| (sexp.list ses) := format.of_string $ "(" ++ (" ".intercalate (ses.map $ format.to_string ∘ sexp_to_format)) ++ ")"

meta instance sexp_has_to_format {α} [has_to_format α] : has_to_format (sexp α) :=
⟨sexp_to_format⟩

end sexp

-- #eval format.to_string $ sexp_to_format $ sexp.list [(sexp.atom 1), (sexp.atom 2), (sexp.atom 3)]

open expr

section sexp_of_expr

-- def sexp.concat {α} : (list $ sexp α) → (list $ sexp α) → sexp α :=
-- λ xs ys, sexp.list $ xs ++ ys

meta def sexp.concat {m} [monad m] [monad_fail m] {α} : (sexp α) → (sexp α) → m (sexp α)
| (sexp.list xs) (sexp.list ys) := pure (sexp.list $ xs ++ ys)
| _ _ := monad_fail.fail "sexp.concat failed"

local infix `<+>`:50 := sexp.concat -- TODO(jesse): just write an applicative instance, don't want to think about `seq` now though

meta def sexp.map {α β : Type*} (f : α → β) : sexp α → sexp β
| (sexp.atom x) := (sexp.atom $ f x)
| (sexp.list xs) := (sexp.list $ sexp.map <$> xs)

meta instance : functor sexp :=
{map := by apply sexp.map}

def mk_type_ascription : sexp string → sexp string → sexp string := λ s₁ s₂, sexp.list [(sexp.atom ":"), s₁, s₂]

-- TODO(jesse): supply version with even more type annotations
meta def sexp_of_expr : (option ℕ) → expr → tactic (sexp string) := λ fuel ex, do {
  match fuel with
  | none := pure ()
  | (some x) := when (x = 0) $ tactic.fail "sexp_of_expr fuel exhausted"
  end,
  match ex with
  | e@(var k) := (sexp.list [sexp.atom "var"]) <+> (sexp.list [sexp.atom (to_string k)])
  | e@(sort l) := (sexp.list [sexp.atom "sort"]) <+> (sexp.list [sexp.atom (to_string l)])
  | e@(const nm ls) := pure $ sexp.atom nm.to_string
  | e@(mvar un pt tp) := do tp_sexp ← sexp_of_expr ((flip nat.sub 1) <$> fuel) tp, pure $ mk_type_ascription (sexp.atom pt.to_string) tp_sexp
  | e@(local_const un pt binder_info tp) := do {
    tp_sexp ← sexp_of_expr ((flip nat.sub 1) <$> fuel) tp,
    -- pure $ flip mk_type_ascription tp_sexp $ sexp.list [sexp.atom pt.to_string] -- note: drop binder info for now
   pure (sexp.atom pt.to_string)
  }
  | e@(app e₁ e₂) := (λ s₁ s₂, sexp.list [s₁, s₂]) <$> sexp_of_expr ((flip nat.sub 1) <$> fuel) e₁ <*> sexp_of_expr ((flip nat.sub 1) <$> fuel) e₂
  -- | e@(app e₁ e₂) := sexp.list <$> ((::) <$> (sexp_of_expr ((flip nat.sub 1) <$> fuel) $ get_app_fn e) <*> (get_app_args e).mmap (sexp_of_expr ((flip nat.sub 1) <$> fuel)))
  | e@(lam var_name b_info var_type body) := do {
    ⟨[b], e'⟩ ← tactic.open_n_lambdas e 1,
    sexp.list <$> do {
      b_sexp ← sexp_of_expr ((flip nat.sub 1) <$> fuel) b,
      b_tp_sexp ← sexp_of_expr ((flip nat.sub 1) <$> fuel) var_type,
      body_sexp ← sexp_of_expr ((flip nat.sub 1) <$> fuel) e',
      pure $ [sexp.atom "LAMBDA", mk_type_ascription (b_sexp) b_tp_sexp, body_sexp]
    }
  }
  | e@(pi var_name b_info var_type body) := do {
    ⟨[b], e'⟩ ← tactic.open_n_pis e 1,
    sexp.list <$> do {
      b_sexp ← sexp_of_expr ((flip nat.sub 1) <$> fuel) b,
      b_tp_sexp ← sexp_of_expr ((flip nat.sub 1) <$> fuel) var_type,
      body_sexp ← sexp_of_expr ((flip nat.sub 1) <$> fuel) e',
      pure $ [sexp.atom "PI", mk_type_ascription (b_sexp) b_tp_sexp, body_sexp]
    }
  }
  -- reduce let expressions before sexpr serialization
  | e@(elet var_name var_type var_assignment body) := sexp_of_expr ((flip nat.sub 1) <$> fuel) e.reduce_let
  | e@(macro md deps) := 
    sexp.list <$> do {
      deps_sexp_list ← sexp.list <$> (deps.mmap $ sexp_of_expr (((flip nat.sub 1) <$> fuel))),
      let deps_sexp := sexp.list [sexp.atom "MACRO_DEPS", deps_sexp_list],
      pure $ [sexp.atom "MACRO", sexp.atom (expr.macro_def_name md).to_string, deps_sexp]
    }
  end
}

meta def flattened_sexp_of_expr (e : expr) : tactic string :=
(format.to_string ∘ format.flatten ∘ has_to_format.to_format) <$> sexp_of_expr none e

end sexp_of_expr