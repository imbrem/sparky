import Mathlib.Init.Algebra.Order
import Mathlib.Order.RelIso.Basic
import Mathlib.Order.Synonym
import Mathlib.Data.Sigma.Order
import Mathlib.Data.Sum.Order

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