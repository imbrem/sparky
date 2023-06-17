import Mathlib.Init.Set
import Mathlib.Algebra.Group.Defs

def ProgramOrder (M: Type) [Monoid M] (A: Type): Type := Option A × M

def ProgramOrders (M: Type) [Monoid M] (A: Type): Type := Set (ProgramOrder M A)

instance (M: Type) [Monoid M] (A: Type): Singleton (Option A × M) (ProgramOrders M A) := {
  singleton := Set.singleton
}
instance (M: Type) [Monoid M] (A: Type): Membership (Option A × M) (ProgramOrders M A) := {
  mem := Set.Mem
}

instance (M: Type) [Monoid M]: Monad (ProgramOrders M) := {
  pure := λa => { ⟨ some a, 1 ⟩  },
  map := λf A p => ∃a ∈ A, match a with
    | ⟨some a, Ea⟩ => p = ⟨some (f a), Ea⟩
    | ⟨none, Ea⟩ => p = ⟨none, Ea⟩, 
  bind := λA f p => ∃a ∈ A, match a with 
    | ⟨some a, Ea⟩ => ∃b ∈ f a, p = ⟨b.fst, Ea * b.snd⟩    
    | ⟨none, Ea⟩ => p = ⟨none, Ea⟩,
}

instance (M: Type) [Monoid M]: LawfulMonad (ProgramOrders M) := {
  map_const := rfl,
  id_map := λA => by
    funext ⟨a, Ea⟩
    apply propext
    apply Iff.intro
    intro ⟨⟨b, Eb⟩, HbA, Hb⟩
    cases b <;> exact Hb ▸ HbA
    intro HA
    cases a with
    | some a => exact ⟨⟨some a, Ea⟩, HA, rfl⟩
    | none => exact ⟨⟨none, Ea⟩, HA, rfl⟩
  ,
  seqLeft_eq := λA B => by
    funext ⟨p, Ep⟩
    apply propext
    apply Iff.intro
    intro ⟨⟨a, Ea⟩, HA, Ha⟩
    cases a with
    | some a => 
      have ⟨⟨a', Ea'⟩, ⟨⟨b, Eb⟩, HB, Hb⟩, Ha'⟩ := Ha;
      sorry
    | none => 
      exact ⟨⟨none, Ea⟩, ⟨⟨none, Ea⟩, HA, rfl⟩, Ha⟩
    intro ⟨a, Ea⟩
    sorry  
    ,
  seqRight_eq := λA B => sorry,
  pure_seq := λf A => sorry,
  bind_pure_comp := λf A => sorry,
  bind_map := λf A => sorry,
  pure_bind := λa f => sorry,
  bind_assoc := λA f g => sorry
}