import Mathlib.Data.Set.Finite

import Sparky.Pom

structure PomIso {L} (α β: Pom L) extends RelIso α.order.le β.order.le :=
  action_eq: ∀{e: α.carrier}, α.action e = β.action (toFun e)

@[refl]
protected def PomIso.refl {L} (α: Pom L): PomIso α α := {
  toRelIso := RelIso.refl _,
  action_eq := rfl
}

@[trans]
protected def PomIso.trans {L} {α β γ: Pom L} (φ: PomIso α β) (ψ: PomIso β γ): PomIso α γ := {
  toRelIso := RelIso.trans φ.toRelIso ψ.toRelIso,
  action_eq := λ{_} => by rw [φ.action_eq, ψ.action_eq]; rfl
}

@[symm]
protected def PomIso.symm {L} {α β: Pom L} (φ: PomIso α β): PomIso β α := {
  toRelIso := RelIso.symm φ.toRelIso,
  action_eq := λ{_} => by simp [φ.action_eq]
}

theorem PomIso.infinite_iff {L} {α β: Pom L} (φ: PomIso α β): Infinite α ↔ Infinite β
  := φ.toEquiv.infinite_iff

theorem PomIso.empty_iff {L} {α β: Pom L} (φ: PomIso α β): IsEmpty α ↔ IsEmpty β
  := ⟨
    λH => IsEmpty.mk (λe => H.elim (φ.invFun e)),
    λH => IsEmpty.mk (λe => H.elim (φ.toFun e))
  ⟩

def PomIso.symm_toRelIso {L} {α β: Pom L} (φ: PomIso α β): φ.symm.toRelIso = φ.toRelIso.symm 
  := rfl
def PomIso.symm_toEquiv {L} {α β: Pom L} (φ: PomIso α β): φ.symm.toEquiv = φ.toEquiv.symm 
  := rfl

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

def PomIso.seq {L} {α β α' β': Pom L} 
  (Iα: PomIso α α') (Iβ: PomIso β β')
  : PomIso (α.seq β) (α'.seq β')
  := {
    toRelIso := RelIso.sumLexCongr Iα.toRelIso Iβ.toRelIso,
    action_eq := λ{e} => 
      by 
        cases e <;> 
        simp [
          Pom.seq, Equiv.sumCongr, RelIso.sumLexCongr, 
          Iα.action_eq, Iβ.action_eq
        ]
  }

def PomIso.par {L} {α β α' β': Pom L} 
  (Iα: PomIso α α') (Iβ: PomIso β β')
  : PomIso (α.par β) (α'.par β')
  := {
    toEquiv := Equiv.sumCongr Iα.toEquiv Iβ.toEquiv,
    map_rel_iff' := λ{a b} => by
      cases a <;> cases b <;>
      simp [Pom.par, Iα.map_rel_iff, Iβ.map_rel_iff]
    action_eq := λ{e} => by 
      cases e <;> 
      simp [Pom.par, Equiv.sumCongr, Iα.action_eq, Iβ.action_eq]
  }