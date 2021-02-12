/- Author: E.W.Ayers © 2019.

Some helpers for dealing with monads etc.
-/
import control.monad.writer control.fold

universes u v

section
  /- Having a writer with append is really useful! -/
  def writer_m (ω : Type) (α : Type) := ω × α
  variables {ω : Type} [has_append ω] [has_emptyc ω] {α : Type}
  instance writer_m.is_monad : monad (writer_m ω) :=
  { pure := λ α a, (∅, a)
  , bind := λ α β ⟨w,a⟩ f, let ⟨w₂,b⟩ := f a in ⟨w ++ w₂, b⟩
  }
  def writer_m.tell : ω → writer_m ω unit
  | x := (x, ())
  def writer_m.run : writer_m ω α → ω × α := id
end

namespace writer_t

  variables {ω : Type u} {m : Type u → Type v} [monad m] {α β : Type u} [has_emptyc ω] [has_append ω]

  instance monad_of_append : monad (writer_t ω m) :=
  @writer_t.monad ω m _ ⟨∅⟩ ⟨(++)⟩

  instance lift_of_empty : has_monad_lift m (writer_t ω m) :=
  ⟨λ α, @writer_t.lift _ _ _ _ ⟨∅⟩⟩

end writer_t

def list_writer_t (σ : Type u) := writer_t (free_monoid σ)

namespace list_writer_t
  local attribute [reducible] list_writer_t free_monoid
  variables {σ : Type u} {m : Type u → Type v} [monad m]
  instance : monad (list_writer_t σ m) := by apply_instance
  instance : monad_writer (list σ) (list_writer_t σ m) := by apply_instance

end list_writer_t

namespace alternative

  section
    variables  {T S : Type u → Type u} [applicative T] [alternative S]
    instance : alternative (T ∘ S) :=
    { pure    := λ α x, (pure (pure x) : T (S _)),
      failure := λ x, (pure $ failure : T (S _)),
      seq     := λ α β f x, show T(S β), from pure (<*>) <*> f <*> x,
      orelse  := λ α a b, show T(S α), from pure (<|>) <*> a <*> b
    }
  end

  variables {T : Type u → Type v} [alternative T] {α β : Type u}

  def returnopt : option α → T α
  | none := failure
  | (some x) := pure x

  def optreturn : T α → T (option α)
  | t := (some <$> t) <|> (pure none)

  def is_ok {T : Type → Type v} [alternative T] {α : Type}:  T α → T (bool)
  | t := (t *> pure (tt)) <|> pure (ff)

  def mguard {T : Type → Type v} [alternative T] [monad T]: T bool → T unit
  | c := do b ← c, if b then pure () else failure

  variables [monad T]

  meta def repeat (t : T α) : T (list α) :=
  (pure list.cons <*> t <*> (pure punit.star >>= λ _, repeat)) <|> pure []

end alternative

def except.flip {ε : Type u} {α : Type v} : except ε α → except α ε
| e := except.rec except.ok except.error e

instance monad_except.of_statet {ε σ} {m : Type → Type} [monad m] [monad_except ε m] : monad_except ε (state_t σ m) :=
{ throw := λ α e, state_t.lift $ throw e
, catch := λ α S e, ⟨λ s, catch (state_t.run S s) (λ x, state_t.run (e x) s)⟩ -- [note] alternatively, you could propagate the state.
}

instance monad_except.alt {ε} [inhabited ε] {m : Type → Type} [monad m] [monad_except ε m] : alternative m :=
{ failure := λ α,throw $ inhabited.default ε
, orelse := λ α x y, monad_except.orelse x y
}

def monad_state.hypothetically {m : Type → Type} [monad m] {σ α : Type} [monad_state σ m] : m α → m α
| m := do s ← get, a ← m, put s, pure a

notation `⍐` := monad_lift