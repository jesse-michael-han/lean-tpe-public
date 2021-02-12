/- Author: E.W.Ayers © 2019.

(Potentially buggy) implementation of a priority queue.
-/
import .table

universe u

structure queue (α : Type u) :=
(l : list α)
(r : list α)

namespace queue

variables {α : Type u}

def empty : queue α := ⟨[],[]⟩

instance : has_emptyc (queue α) := ⟨empty⟩

instance : inhabited (queue α) := ⟨empty⟩

def enqueue : α → queue α → queue α
| a ⟨l,r⟩ := ⟨l,a::r⟩

def peek : queue α → option α
| ⟨h::l,r⟩ := some h
| ⟨[],r⟩ := list.olast r

def dequeue : queue α → option (α × queue α)
| ⟨h::l,r⟩ := some (h, ⟨l,r⟩)
| ⟨[], r⟩ :=
  match list.reverse r with
  | (h::l) := some (h, queue.mk l [])
  | [] := none
  end

def is_empty : queue α → bool
| ⟨[],[]⟩ := tt
| _ := ff

def foldl {β} (f : β → α → β) : β → queue α → β
| b ⟨l,r⟩ := r.foldr (function.swap f) $ l.foldl f b

def mfoldl {M} [monad M] {β} (f : β → α → M β) : β → queue α → M β
| b ⟨l,r⟩ := l.mfoldl f b >>= λ b, r.mfoldr (function.swap f) b

def to_list : queue α → list α | ⟨l,r⟩ := l ++ r.reverse

def of_list : list α → queue α | l := ⟨l,[]⟩

def append : queue α → queue α → queue α
| ⟨l1,r1⟩ ⟨l2,r2⟩ := ⟨l1,r2 ++ l2.reverse ++ r1⟩
-- assuming the 2nd queue is shorter than 1st queue.

instance : has_append (queue α) := ⟨append⟩

private def shunt : queue α → queue α
| ⟨l,r⟩ := ⟨l ++ r.reverse, []⟩

protected def map {β} (f : α → β) : queue α → queue β
| ⟨l,r⟩ := ⟨f <$> l, f <$> r⟩

instance : functor queue := { map := λ α β, queue.map}

-- def traverse {M} [applicative M] {α β} (f : α → M β) (q : queue α) : M (queue α) :=
-- list.traverse f (shunt q) >>= λ l, pure ⟨l,[]⟩

def has (f : α → bool) : queue α → bool | ⟨l,r⟩ := list.any l f || list.any r f

protected def mem : α → queue α → Prop
| a ⟨l,r⟩ := a ∈ l ∨ a ∈ r

instance : has_mem α (queue α) := ⟨queue.mem⟩

instance [decidable_eq α] {a:α} {q:queue α}: decidable (a ∈ q) :=
begin cases q with l r, show decidable (a ∈ l ∨ a ∈ r), apply_instance end

def enqueue_no_dup [decidable_eq α] : α → queue α → queue α
| a q := if a ∈ q then q else enqueue a q

end queue

/-- Priority queue. Lower `p a` means it is more prioritised.  -/
meta def pqueue {α : Type} (p : α → ℤ) :=
dict ℤ (queue α)

namespace pqueue

open queue

variables {α : Type} {p : α → ℤ}

meta instance : has_emptyc (pqueue p) :=
dict.has_emptyc

meta def empty : pqueue p := has_emptyc.emptyc

meta def enqueue : α → pqueue p → pqueue p
| a := dict.modify (queue.enqueue a ∘ option.iget) $ p a

meta def enqueue_no_dup [decidable_eq α] : α → pqueue p → pqueue p
| a := dict.modify (queue.enqueue_no_dup a ∘ option.iget) $ p a

meta def enqueue_many : list α → pqueue p → pqueue p
| l q := list.foldl (function.swap enqueue) q l

meta def enqueue_many_no_dup [decidable_eq α]: list α → pqueue p → pqueue p
| items q := list.foldl (function.swap enqueue_no_dup) q items

meta def dequeue : pqueue p → option (α × pqueue p)
| pq := do
  q ← dict.min pq,
  (a,q) ← q.dequeue, -- should not be empty
  if is_empty q then pure (a, dict.erase (p a) pq) else
  pure (a, dict.insert (p a) q pq)

meta def of_list : list α → pqueue p
| l := l.foldl (λ acc a, enqueue a acc) ∅

meta def append : pqueue p → pqueue p → pqueue p :=
dict.merge_with $ λ k, (++)

meta instance : has_append (pqueue p) := ⟨append⟩

meta def fold {β} (f : β → α → β) : β → pqueue p → β :=
dict.fold (λ b k, queue.foldl f b)

meta def mfold {T} [monad T] {β} (f : β → α → T β) : β → pqueue p → T β :=
dict.mfold (λ b k, queue.mfoldl f b)

meta def has (f : α → bool) : pqueue p → bool :=
dict.any $ λ _, queue.has f -- [todo] arbitrate `any` vs `has` naming

meta def to_list : pqueue p → list α :=
list.join ∘ list.map prod.snd ∘ dict.to_list ∘ dict.map queue.to_list

meta instance has_pp [has_to_tactic_format α] : has_to_tactic_format (pqueue p) :=
⟨tactic.pp ∘ to_list⟩

meta instance has_to_format [has_to_format α] : has_to_format (pqueue p) :=
⟨λ p, format!"{p.to_list}"⟩

meta instance : has_sizeof (pqueue p) := by apply_instance

meta def size : pqueue p → ℕ := λ pq,
pq.fold (λ acc pq, nat.succ acc) 0

end pqueue

