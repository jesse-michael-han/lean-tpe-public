import algebra.archimedean
import data.list
import all

import .trythis

namespace nng

lemma add_assoc (a b c : ℕ)
  : (a + b) + c = a + (b + c) :=
begin
  -- rw [nat.add_assoc, nat.add_comm a],
  simp [nat.add_assoc]
end

open nat

lemma succ_add (a b : ℕ)
  : succ a + b = succ (a + b) :=
begin
  -- rw [← add_succ, add_succ, succ_add]
  apply succ_add; rw [nat.add_comm, nat.zero_add]; refl
end

lemma add_right_comm (a b c : ℕ)
  : a + b + c = a + c + b :=
begin
  -- rw [add_comm a, add_comm a, add_assoc],
  -- rw [add_comm b, add_comm a, add_assoc]
  rw add_right_comm; refl
end

lemma succ_mul (a b : ℕ)
  : succ a * b = a * b + b :=
begin
  -- rw [← nat.succ_mul],
  rw [← add_one, succ_mul]
end

theorem add_le_add_right {a b : ℕ}
  : a ≤ b → ∀ t, (a + t) ≤ (b + t) :=
begin
  -- intros h t,
  -- rw [nat.add_comm a t, nat.add_comm b t],
  -- apply nat.add_le_add_left h _
  apply nat.add_le_add_right
end

theorem mul_left_cancel (a b c : ℕ) (ha : a ≠ 0)
  : a * b = (a + 0) * c → b = 1 * c :=
begin
  -- simp,
  -- rintro (⟨⟨h₁, h₂⟩, rfl⟩ | ⟨⟨h₁, h₂⟩, rfl⟩),
  -- assumption,
  -- contradiction
  simpa [one_mul] using (mul_left_inj' ha).mp
end

lemma lt_aux_two (a b : ℕ) : succ a ≤ b → a ≤ b ∧ ¬ (b ≤ a) :=
begin
  intro h, exact ⟨nat.le_of_succ_le h, not_le_of_gt h⟩
end

universe u
variables {R : Type u} [linear_ordered_ring R] [floor_ring R] {x : R}

lemma floor_ciel (z : ℤ) : z = ⌈(z:R)⌉ :=
begin
  -- rw [ceil, ← int.cast_neg, floor_coe, neg_neg]
  simp
end

example (x y : ℤ) : (- - x) - y = -(y - x) :=
begin
  -- simp
  simp
end

variables {G : Type u} [group G]

example (x y z : G) : (x * z) * (z⁻¹ * y) = x * y :=
begin
  -- group
  rw [←mul_assoc, mul_inv_cancel_right]
end

open list

example {α: Type u} (a : α) (l : list α)
  : list.reverse (l ++ [a]) = a :: l.reverse :=
begin
  simp
  -- induction l, {refl}, {simp only [*, cons_append, reverse_cons, append_assoc, reverse_nil, perm.nil, append_nil, perm.cons], simp}
end

end nng
