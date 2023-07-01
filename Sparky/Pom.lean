import Mathlib.Data.Sigma.Order
import Mathlib.Data.Sum.Order

structure Pom (L: Type) :=
  carrier: Type
  order: PartialOrder carrier
  action: carrier -> L

instance {L}: CoeOut (Pom L) (Type) := {
  coe := Pom.carrier
}

def Pom.empty (L: Type): Pom L := {
  carrier := Empty,
  order := {
    le := λ_ _ => True,
    le_refl := (λa => match a with .),
    le_trans := (λa => match a with .),
    le_antisymm := (λa => match a with .)
  },
  action := λe => match e with.
}

def PomFamily (N: Type) [PartialOrder N] (L) := N -> Pom L

def Pom.sigma {L} {N: Type} [PartialOrder N] (F: PomFamily N L): Pom L := {
  carrier := Lex (Sigma (λn => (F n).carrier)),
  order := @Sigma.Lex.partialOrder _ _ _ (λn => (F n).order),
  action := (λ⟨n, e⟩ => (F n).action e)
}

abbrev PomFamily.toPom {N} [PartialOrder N] {L} (F: PomFamily N L): Pom L 
  := Pom.sigma F

def Pom.seq {L} (α β: Pom L): Pom L := {
  carrier := Lex (α.carrier ⊕ β.carrier),
  order := @Sum.Lex.partialOrder _ _ α.order β.order,
  action := Sum.elim α.action β.action
}

def Pom.par_order {L} (α β: Pom L)
  : PartialOrder (α.carrier ⊕ β.carrier)
  := @Sum.instPartialOrderSum _ _ α.order β.order

@[simp]
def Pom.par_order_ll {L} {α β: Pom L}
  {a: α.carrier} {b: α.carrier}
  : ((α.par_order β).le (Sum.inl a) (Sum.inl b)) <-> α.order.le a b
  := by simp [LE.le, par_order]

@[simp]
def Pom.par_order_lr {L} {α β: Pom L}
  {a: α.carrier} {b: β.carrier}
  : ¬((α.par_order β).le (Sum.inl a) (Sum.inr b))
  := by simp [LE.le, par_order]

@[simp]
def Pom.par_order_rl {L} {α β: Pom L}
  {a: α.carrier} {b: β.carrier}
  : ¬((α.par_order β).le (Sum.inr b) (Sum.inl a))
  := by simp [LE.le, par_order]

@[simp]
def Pom.par_order_rr {L} {α β: Pom L}
  {a: β.carrier} {b: β.carrier}
  : ((α.par_order β).le (Sum.inr a) (Sum.inr b)) <-> β.order.le a b
  := by simp [LE.le, par_order]

def Pom.par {L} (α β: Pom L): Pom L := {
  carrier := α.carrier ⊕ β.carrier,
  order := α.par_order β,
  action := Sum.elim α.action β.action
}