import Mathlib.Init.Algebra.Order
import Mathlib.Order.RelIso.Basic
import Mathlib.Order.Synonym
import Mathlib.Data.Sigma.Order
import Mathlib.Data.Sum.Order
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Defs

open Classical

structure Pom (L: Type) :=
  carrier: Type
  order: PartialOrder carrier
  action: carrier -> L

structure PomIso {L} (α β: Pom L) extends RelIso α.order.le β.order.le :=
  action_eq: ∀e: α.carrier, α.action e = β.action (toFun e)

def PomIso.refl {L} (α: Pom L): PomIso α α := {
  toRelIso := RelIso.refl _,
  action_eq := λ_ => rfl
}

def PomIso.trans {L} {α β γ: Pom L} (φ: PomIso α β) (ψ: PomIso β γ): PomIso α γ := {
  toRelIso := RelIso.trans φ.toRelIso ψ.toRelIso,
  action_eq := λ_ => by rw [φ.action_eq, ψ.action_eq]; rfl
}

def PomIso.symm {L} {α β: Pom L} (φ: PomIso α β): PomIso β α := {
  toRelIso := RelIso.symm φ.toRelIso,
  action_eq := λ_ => by simp [φ.action_eq]
}

def Pom.sigma {L} {N: Type} [PartialOrder N] (F: N -> Pom L): Pom L := {
  carrier := Lex (Sigma (λn => (F n).carrier)),
  order := @Sigma.Lex.partialOrder _ _ _ (λn => (F n).order),
  action := (λ⟨n, e⟩ => (F n).action e)
}

def PomIso.sigma {L} {N: Type} [PartialOrder N] {F: N -> Pom L} {G: N -> Pom L}
  (I: ∀n: N, PomIso (F n) (G n)):
  PomIso (Pom.sigma F) (Pom.sigma G)
  := {
    toRelIso := ⟨
      Equiv.sigmaCongr (Equiv.refl _) (λn => (I n).toEquiv),
      by {
        intro ⟨i, a⟩;
        intro ⟨j, b⟩;
        apply Iff.trans Sigma.lex_iff;
        apply Iff.trans _ Sigma.lex_iff.symm;
        apply Iff.or Iff.rfl;
        apply Iff.of_eq;
        apply congr rfl;
        funext v;
        cases v;
        simp [Equiv.sigmaCongr, Equiv.sigmaCongrRight, (I i).map_rel_iff]
      }
    ⟩,
    action_eq := by {
      intro ⟨i, e⟩;
      simp [Pom.sigma, Equiv.sigmaCongr, (I i).action_eq]
    }
  }

def Pom.seq {L} (α β: Pom L): Pom L := {
  carrier := Lex (α.carrier ⊕ β.carrier),
  order := @Sum.Lex.partialOrder _ _ α.order β.order,
  action := Sum.elim α.action β.action
}

def PomIso.seq {L} {α β α' β': Pom L} 
  (Iα: PomIso α α') (Iβ: PomIso β β')
  : PomIso (α.seq β) (α'.seq β')
  := {
    toRelIso := RelIso.sumLexCongr Iα.toRelIso Iβ.toRelIso,
    action_eq := λe => 
      by 
        cases e <;> 
        simp [
          Pom.seq, Equiv.sumCongr, RelIso.sumLexCongr, 
          Iα.action_eq, Iβ.action_eq
        ]
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

def PomIso.par {L} {α β α' β': Pom L} 
  (Iα: PomIso α α') (Iβ: PomIso β β')
  : PomIso (α.par β) (α'.par β')
  := {
    toEquiv := Equiv.sumCongr Iα.toEquiv Iβ.toEquiv,
    map_rel_iff' := λ{a b} => by
      cases a <;> cases b <;>
      simp [Pom.par, Iα.map_rel_iff, Iβ.map_rel_iff]
    action_eq := λe => by 
      cases e <;> 
      simp [Pom.par, Equiv.sumCongr, Iα.action_eq, Iβ.action_eq]
  }

structure SubPom {L} (P: Pom L): Type := 
  contains: Set P.carrier

def SubPom.full {L} (P: Pom L): SubPom P := ⟨ λ_ => True ⟩
def SubPom.empty {L} (P: Pom L): SubPom P := ⟨ λ_ => False ⟩ 
def SubPom.union {L} {P: Pom L} (A B: SubPom P): SubPom P := 
   ⟨ λe => A.contains e ∨ B.contains e ⟩
def SubPom.intersection {L} {P: Pom L} (A B: SubPom P): SubPom P 
  := ⟨ λe => A.contains e ∧ B.contains e ⟩ 
def SubPom.complement {L} {P: Pom L} (A: SubPom P): SubPom P 
  := ⟨ λe => ¬(A.contains e) ⟩
def SubPom.deletion {L} {P: Pom L} (A R: SubPom P): SubPom P
  := ⟨ λe => A.contains e ∧ ¬(R.contains e) ⟩  

def SubPom.intersection_comm {L} {P: Pom L} (A B: SubPom P)
  : A.intersection B = B.intersection A
  := by simp [intersection, and_comm]

def SubPom.union_comm {L} {P: Pom L} (A B: SubPom P)
  : A.union B = B.union A
  := by simp [union, or_comm]

def SubPom.intersection_full {L} {P: Pom L} (A: SubPom P)
  : A.intersection (full P) = A
  := by simp [intersection, full]

def SubPom.full_intersection {L} {P: Pom L} (A: SubPom P)
  : (full P).intersection A = A
  := by simp [intersection, full]

def SubPom.sigma {L} {N: Type} [PartialOrder N] 
  {F: N -> Pom L} (SF: (n: N) -> SubPom (F n))
  : SubPom (Pom.sigma F)
  := ⟨ λ⟨n, e⟩ => (SF n).contains e ⟩

def SubPom.seq {L} {A B: Pom L} (SA: SubPom A) (SB: SubPom B)
  : SubPom (A.seq B)
  := ⟨ Sum.elim SA.contains SB.contains ⟩

def SubPom.par {L} {A B: Pom L} (SA: SubPom A) (SB: SubPom B)
  : SubPom (A.par B)
  := ⟨ Sum.elim SA.contains SB.contains ⟩

def SubPom.carrier {L} {P: Pom L} (S: SubPom P): Type
  := ↑S.contains

def SubPom.order {L} {P: Pom L} (S: SubPom P): PartialOrder S.carrier
  := @Subtype.partialOrder P.carrier P.order S.contains

def SubPom.action {L} {P: Pom L} (S: SubPom P) (p: S.carrier): L
  := P.action p.val

def SubPom.toPom {L} {P: Pom L} (S: SubPom P): Pom L := {
  carrier := S.carrier,
  order := S.order,
  action := S.action
}

def Pom.finite {L} (P: Pom L): Prop
  := Finite P.carrier

def Pom.infinite {L} (P: Pom L): Prop
  := Infinite P.carrier

def SubPom.finite {L} {P: Pom L} (S: SubPom P): Prop
  := Finite S.carrier

def SubPom.infinite {L} {P: Pom L} (S: SubPom P): Prop
  := Infinite S.carrier

def Pom.pred {L} (P: Pom L) (p: P.carrier): SubPom P
  := ⟨ P.order.le p ⟩

def SubPom.pred {L} {P: Pom L} (A: SubPom P) (p: A.carrier) 
  := A.intersection (P.pred p.val)

def SubPom.full_pred_pred_full {L} (P: Pom L) (p)
  : (full P).pred p = P.pred p.val
  := full_intersection (P.pred p.val)

def Pom.finite_pred {L} (α: Pom L) (p: α.carrier): Prop
  := (α.pred p).finite

def Pom.infinite_pred {L} (α: Pom L) (p: α.carrier): Prop
  := (α.pred p).infinite

def SubPom.infinite_pred {L} {α: Pom L} (ρ: SubPom α) (p: ρ.carrier)
  : Prop
  := (ρ.pred p).infinite

theorem Pom.full_carrier_equiv {L} (α: Pom L)
  : α.carrier ≃ (SubPom.full α).carrier
  := ⟨
    λa => ⟨a, True.intro⟩,
    λ⟨a, True.intro⟩ => a,
    λ_ => rfl,
    λ⟨_, _⟩ => rfl
  ⟩

class Ticked (L: Type) :=
  δ: L

structure PomReduces {L} [Ticked L] {α: Pom L} (ρ: SubPom α): Prop :=
  infinite_or_tick: ∀p: α.carrier, 
    ρ.contains p ∨ 
    α.infinite_pred p ∨ 
    α.action p = Ticked.δ
  infinite_preserved: ∀p: ρ.toPom.carrier,
    α.infinite_pred p.val -> ρ.infinite_pred p
  infinite_shared:
    α.infinite -> ρ.infinite
  empty_shared:
    IsEmpty ρ.carrier -> IsEmpty α.carrier

theorem PomReduces.refl {L} [Ticked L] (α: Pom L):
  PomReduces (SubPom.full α)
  := {
    infinite_or_tick := λp => Or.inl True.intro,
    infinite_preserved := λp H => by 
      rw [SubPom.infinite_pred, SubPom.full_pred_pred_full]
      exact H
    infinite_shared := λH => 
      α.full_carrier_equiv.infinite_iff.mp H,
    empty_shared := λH => IsEmpty.mk (λe => H.false ⟨e, True.intro⟩),
  }

theorem PomReduces.empty {L} [Ticked L] {α: Pom L}
  (P: PomReduces (SubPom.empty α))
  : IsEmpty α.carrier
  := sorry

theorem PomReduces.intersection {L} [Ticked L] 
  (α: Pom L)
  (ρ σ: SubPom α)
  : 
  PomReduces ρ 
  -> PomReduces σ 
  -> PomReduces (ρ.intersection σ)
  := sorry 

theorem PomReduces.union {L} [Ticked L]
  (α: Pom L)
  (ρ σ: SubPom α)
  : 
  PomReduces ρ 
  -> PomReduces σ 
  -> PomReduces (ρ.union σ)
  := sorry 

structure PomReduct {L} [Ticked L] (α: Pom L) :=
  shared: SubPom α
  is_reduct: PomReduces shared

def PomReduces.toReduct {L} [Ticked L] {α: Pom L} {ρ: SubPom α} 
  (P: PomReduces ρ):
  PomReduct α
  := {
    shared := ρ,
    is_reduct := P
  }

def PomReduct.refl {L} [Ticked L] (α: Pom L):
  PomReduct α
  := (PomReduces.refl α).toReduct

structure PomEquiv {L} [Ticked L] (α β: Pom L) :=
  reduce_left: PomReduct α
  reduce_right: PomReduct β
  iso: PomIso reduce_left.shared.toPom reduce_right.shared.toPom

theorem PomEquiv.refl {L} [Ticked L] (α: Pom L):
  PomEquiv α α := {
    reduce_left := PomReduct.refl α,
    reduce_right := PomReduct.refl α,
    iso := PomIso.refl _
  }

theorem PomEquiv.symm {L} [Ticked L] {α β: Pom L} (P: PomEquiv α β)
  : PomEquiv β α := {
    reduce_left := P.reduce_right,
    reduce_right := P.reduce_left,
    iso := P.iso.symm 
  }

theorem PomEquiv.trans {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β)
  (Q: PomEquiv β γ)
  : PomEquiv α γ
  := sorry