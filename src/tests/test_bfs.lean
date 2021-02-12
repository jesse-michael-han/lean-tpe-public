import evaluation
import backends.bfs.baseline


import all
open baseline

example {p q : Prop} (h₁ : p) (h₂ : q) : p ∧ q :=
begin
 tidy
end

universe u
example {α : Type u} (p : α → Prop) [decidable_pred p] (l : list α) :
  list.partition p l = (list.filter p l, list.filter (not ∘ p) l) :=
begin
  simp at *
end

-- example : ∀ (b : bool) (n : ℕ), (nat.bit b n).bodd = b :=
-- begin
--   -- simp at *
--   tidy_bfs_proof_search 25 tt 1
-- end


