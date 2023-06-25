import Mathlib.Init.Set
import Mathlib.Data.Set.Lattice
import Mathlib.Algebra.Group.Defs

def ProgramOrder (M: Type) [Monoid M] (A: Type): Type := Option A × M

instance (M: Type) [Monoid M]: Monad (ProgramOrder M) := {
  pure := λa => ⟨some a, 1⟩,
  bind := λ⟨a, Ea⟩ f => match a with 
    | some a => let ⟨b, Eb⟩ := f a; ⟨b, Ea * Eb⟩
    | none => ⟨none, Ea⟩
}

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
  seqLeft := λA B => ⋃ a ∈ A, {⟨
    a.fst <* b.fst, 
    a.snd * ((a.fst *> b.snd).getD 1)
  ⟩ | b ∈ B ()},
  seqRight := λA B => ⋃ a ∈ A, {⟨
    a.fst *> b.fst, 
    a.snd * ((a.fst *> b.snd).getD 1)
  ⟩ | b ∈ B ()},
  seq := λA B => ⋃ a ∈ A, {⟨
    a.fst <*> b.fst, 
    a.snd * ((a.fst *> b.snd).getD 1)
  ⟩ | b ∈ B ()},
  bind := λA f => ⋃ a ∈ A, 
    { (b.fst, a.snd * b.snd) | b ∈ ProgramOrders.lift_opt f a.fst }
}

example: some 3 <* @Option.none Nat = none
  := rfl

theorem ProgramOrders.none_id_map {M: Type} [Monoid M] {α β: Type}
  {A: ProgramOrders M α} {E: M} (H: ⟨none, E⟩ ∈ A) (f: α -> β)
  : ⟨none, E⟩ ∈ f <$> A
  := ⟨_, H, rfl⟩

instance (M: Type) [Monoid M]: LawfulMonad (ProgramOrders M) := {
  map_const := rfl,
  id_map := λA => Set.ext λ⟨a, Ea⟩ => ⟨
      λ ⟨⟨b, Eb⟩, HbA, Hb⟩ => by cases b <;> exact Hb ▸ HbA,
      λHA => ⟨⟨a, Ea⟩, HA, by cases a <;> rfl⟩
    ⟩
  ,
  seqLeft_eq := λA B => Set.ext λ_ => ⟨
      λ⟨X, ⟨⟨x, Ex⟩, Hx⟩, HX⟩ => by
          cases Hx
          have ⟨Y, ⟨Hx, Hy⟩, HY⟩ := HX
          cases Hy
          have ⟨⟨y, Ey⟩, Hy, Hy'⟩ := HY
          cases Hy'
          cases x <;> cases y <;> exact ⟨
            _, 
            ⟨_, rfl⟩, 
            _,
            ⟨⟨_, Hx, rfl⟩, rfl⟩,
            _,
            Hy,
            rfl
          ⟩,
      λ⟨X, ⟨⟨⟨f, Ef⟩, Hf⟩, Hp⟩⟩ => by
        cases Hf
        have ⟨Y, ⟨⟨Hy, HY⟩, Hp⟩⟩ := Hp
        cases HY
        have ⟨⟨x, Ex⟩, Hb, HB⟩ := Hp 
        cases HB
        have ⟨⟨y, Ey⟩, Hb', Heb'⟩ := Hp
        have ⟨⟨z, Ez⟩, Hz, Hez⟩ := Hy
        cases Hez
        cases x <;>
        cases y <;>
        cases z <;>
        exact Set.mem_iUnion.mpr ⟨ 
          _,
          Set.mem_iUnion.mpr ⟨
            Hz, 
            Set.mem_setOf.mpr 
            ⟨_, Hb, rfl⟩
          ⟩
        ⟩
    ⟩
    ,
  seqRight_eq := λA B => Set.ext λ⟨p, Ep⟩ => ⟨ 
    λ⟨X, ⟨⟨x, Ex⟩, Hx⟩, HX⟩ => by
      cases Hx
      have ⟨Y, ⟨Hx, Hy⟩, HY⟩ := HX
      cases Hy
      have ⟨⟨y, Ey⟩, Hy, Hy'⟩ := HY
      cases Hy'
      cases x <;> cases y <;>
      exact ⟨
        _, 
        ⟨_, rfl⟩, 
        _,
        ⟨⟨_, Hx, rfl⟩, rfl⟩,
        _,
        Hy,
        rfl
      ⟩
    ,
    λ⟨X, ⟨⟨⟨f, Ef⟩, Hf⟩, Hp⟩⟩ => by
        cases Hf
        have ⟨Y, ⟨⟨Hy, HY⟩, Hp⟩⟩ := Hp
        cases HY
        have ⟨⟨x, Ex⟩, Hb, HB⟩ := Hp 
        cases HB
        have ⟨⟨y, Ey⟩, Hb', Heb'⟩ := Hp
        have ⟨⟨z, Ez⟩, Hz, Hez⟩ := Hy
        cases Hez
        cases x <;>
        cases y <;>
        cases z <;>
        exact Set.mem_iUnion.mpr ⟨ 
          _,
          Set.mem_iUnion.mpr ⟨
            Hz, 
            Set.mem_setOf.mpr 
            ⟨_, Hb, rfl⟩
          ⟩
        ⟩
  ⟩,
  pure_seq := λf A => Set.ext λ⟨p, Ep⟩ => ⟨
    λ⟨X, ⟨⟨x, Ex⟩, Hx⟩, HX⟩ => by
      cases Hx
      have ⟨Y, ⟨Hx, Hx'⟩, Hy⟩ := HX
      cases Hx
      cases Hx'
      have ⟨z, Hz, Hz'⟩ := Hy;
      cases Hz'
      exact ⟨_, Hz, by simp [Seq.seq, SeqRight.seqRight]⟩,
    λ⟨⟨x, Ex⟩, HA, HX⟩ => by
      cases HX
      exact Set.mem_iUnion.mpr ⟨ 
          _,
          Set.mem_iUnion.mpr ⟨
            rfl, 
            Set.mem_setOf.mpr 
            ⟨_, HA, by simp [Seq.seq, SeqRight.seqRight]⟩
          ⟩
        ⟩
  ⟩,
  bind_pure_comp := λf A => Set.ext λ⟨p, Ep⟩ => ⟨
    λ⟨X, ⟨⟨x, Ex⟩, Hx⟩, HX⟩ => sorry,
    λ⟨X, Hx, HX⟩ => sorry
  ⟩,
  bind_map := λf A => Set.ext λ⟨p, Ep⟩ => ⟨
    sorry,
    sorry
  ⟩,
  pure_bind := λa f => Set.ext λ⟨p, Ep⟩ => ⟨
    sorry,
    sorry
  ⟩,
  bind_assoc := λA f g => Set.ext λ⟨p, Ep⟩ => ⟨
    sorry,
    sorry
  ⟩
}