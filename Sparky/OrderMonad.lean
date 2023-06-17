import Mathlib.Init.Set
import Mathlib.Data.Set.Lattice
import Mathlib.Algebra.Group.Defs

def ProgramOrder (M: Type) [Monoid M] (A: Type): Type := Option A × M

def ProgramOrders (M: Type) [Monoid M] (A: Type): Type := Set (ProgramOrder M A)

instance (M: Type) [Monoid M] (A: Type): Singleton (Option A × M) (ProgramOrders M A) := {
  singleton := Set.singleton
}
instance (M: Type) [Monoid M] (A: Type): Membership (Option A × M) (ProgramOrders M A) := {
  mem := Set.Mem
}

def ProgramOrders.lift_opt {M: Type} [Monoid M] {A B: Type}  (f: A -> ProgramOrders M B)
  : Option A -> ProgramOrders M B
  | some a => f a
  | none => { ⟨none, 1⟩ }

instance (M: Type) [Monoid M]: Monad (ProgramOrders M) := {
  pure := λa => { ⟨ some a, 1 ⟩  },
  map := λf A=> {⟨a.fst.map f, a.snd⟩ | a ∈ A }, 
  bind := λA f => ⋃ a ∈ A, 
    { (b.fst, a.snd * b.snd) | b ∈ ProgramOrders.lift_opt f a.fst }
}

instance (M: Type) [Monoid M]: LawfulMonad (ProgramOrders M) := {
  map_const := rfl,
  id_map := λA => Set.ext λ⟨a, Ea⟩ => ⟨
      λ ⟨⟨b, Eb⟩, HbA, Hb⟩ => by cases b <;> exact Hb ▸ HbA,
      λHA => ⟨⟨a, Ea⟩, HA, by cases a <;> rfl⟩
    ⟩
  ,
  seqLeft_eq := λA B => by
    simp only [SeqLeft.seqLeft, Seq.seq]
    apply Set.ext
    intro ⟨p, Ep⟩
    apply Iff.intro
    intro ⟨X, ⟨⟨x, Ex⟩, Hx⟩, HX⟩
    cases Hx
    have ⟨Y, ⟨Hx, Hy⟩, HY⟩ := HX
    cases Hy
    have ⟨⟨y, Ey⟩, Hy, Hy'⟩ := HY
    cases Hy'
    exact ⟨_, ⟨⟨⟨sorry, sorry⟩, rfl⟩, sorry⟩⟩ 
    sorry
    ,
  seqRight_eq := λA B => sorry,
  pure_seq := λf A => sorry,
  bind_pure_comp := λf A => sorry,
  bind_map := λf A => sorry,
  pure_bind := λa f => sorry,
  bind_assoc := λA f g => sorry
}