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

def Pom.par {L} (α β: Pom L): Pom L := {
  carrier := α.carrier ⊕ β.carrier,
  order := @Sum.instPartialOrderSum _ _ α.order β.order,
  action := Sum.elim α.action β.action
}

def Pom.pred {L} (α: Pom L) (p: α.carrier): Type
  := {q: α.carrier // α.order.le q p}

def Pom.finite_pred {L} (α: Pom L) (p: α.carrier): Prop
  := Finite (α.pred p)

def Pom.infinite_pred {L} (α: Pom L) (p: α.carrier): Prop
  := Infinite (α.pred p)

def SubPom {L} (P: Pom L): Type := P.carrier -> Prop

def SubPom.full {L} (P: Pom L): SubPom P := λ_ => True
def SubPom.empty {L} (P: Pom L): SubPom P := λ_ => False
def SubPom.union {L} {P: Pom L} (A B: SubPom P) := λe => A e ∨ B e
def SubPom.intersection {L} {P: Pom L} (A B: SubPom P) := λe => A e ∧ B e
def SubPom.complement {L} {P: Pom L} (A: SubPom P) := λe => ¬(A e)
def SubPom.deletion {L} {P: Pom L} (A R: SubPom P) := λe => A e ∧ ¬(R e)  

def SubPom.sigma {L} {N: Type} [PartialOrder N] {F: N -> Pom L} (SF: (n: N) -> SubPom (F n))
  : SubPom (Pom.sigma F)
  := λ⟨n, e⟩ => SF n e

def SubPom.seq {L} {A B: Pom L} (SA: SubPom A) (SB: SubPom B): SubPom (A.seq B)
  := Sum.elim SA SB

def SubPom.par {L} {A B: Pom L} (SA: SubPom A) (SB: SubPom B): SubPom (A.par B)
  := Sum.elim SA SB

def SubPom.toPom {L} {P: Pom L} (S: SubPom P): Pom L := {
  carrier := { x: P.carrier // S x },
  order := @Subtype.partialOrder _ P.order S,
  action := λe => P.action e.val --TODO: use builtin?
}

class Ticked (L: Type) :=
  δ: L

structure PomReduces {L} [Ticked L] (α: Pom L) (ρ: SubPom α): Prop :=
  infinite_or_tick: ∀p: α.carrier, 
    ρ p ∨ 
    α.infinite_pred p ∨ 
    α.action p = Ticked.δ
  infinite_preserved: ∀p: ρ.toPom.carrier,
    α.infinite_pred p.val -> ρ.toPom.infinite_pred p
  infinite_shared:
    Infinite α.carrier -> Infinite ρ.toPom.carrier
  empty_shared:
    IsEmpty ρ.toPom.carrier -> IsEmpty α.carrier

theorem PomReduces.refl {L} [Ticked L] (α: Pom L):
  PomReduces α (SubPom.full α)
  := {
    infinite_or_tick := λp => Or.inl True.intro,
    infinite_preserved := λp => sorry,
    infinite_shared := λH => sorry,
    empty_shared := λH => sorry,
  }

theorem PomReduces.empty {L} [Ticked L] {α: Pom L}
  (P: PomReduces α (SubPom.empty α))
  : IsEmpty α.carrier
  := sorry

theorem PomReduces.intersection {L} [Ticked L] 
  (α: Pom L)
  (ρ σ: SubPom α)
  : 
  PomReduces α ρ 
  -> PomReduces α σ 
  -> PomReduces α (ρ.intersection σ)
  := sorry 

theorem PomReduces.union {L} [Ticked L]
  (α: Pom L)
  (ρ σ: SubPom α)
  : 
  PomReduces α ρ 
  -> PomReduces α σ 
  -> PomReduces α (ρ.union σ)
  := sorry 

structure PomReduct {L} [Ticked L] (α: Pom L) :=
  shared: SubPom α
  is_reduct: PomReduces α shared

def PomReduces.toReduct {L} [Ticked L] {α: Pom L} {ρ} 
  (P: PomReduces α ρ):
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