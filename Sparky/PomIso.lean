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

def Pom.unit_sigma_iso {L} (α: Pom L)
  : PomIso α (Pom.sigma (λ_: Unit => α)) := {
  toFun := λa => ⟨(), a⟩,
  invFun := λ⟨_, a⟩ => a,
  left_inv := λ_ => rfl,
  right_inv := λ_ => rfl,
  map_rel_iff' := ⟨
    λH => match H with | Sigma.Lex.right _ _ H => H,
    λH => Sigma.Lex.right _ _ H
  ⟩,
  action_eq := rfl
}

def PomIso.seq2 {L} (α: Fin 2 -> Pom L)
  : PomIso (Pom.sigma α) ((α 0).seq (α 1)) := {
    toFun := λa => match a with 
      | ⟨0, a⟩ => Sum.inl a 
      | ⟨1, a⟩ => Sum.inr a
    invFun := λa => match a with
      | Sum.inl a => ⟨0, a⟩
      | Sum.inr a => ⟨1, a⟩
    left_inv := λ⟨e, _⟩ => match e with | 0 => rfl | 1 => rfl
    right_inv := λa => by cases a <;> rfl
    map_rel_iff' := λ{a} {b} => ⟨
      λH => match a, b, H with
      | ⟨0, a⟩, ⟨0, b⟩, Sum.Lex.inl H => Sigma.Lex.right _ _ H
      | ⟨0, a⟩, ⟨1, b⟩, Sum.Lex.sep _ _ => Sigma.Lex.left _ _ (by simp)
      | ⟨1, a⟩, ⟨0, b⟩, H => by cases H -- Avoid "declaration has metavariables" bug
      | ⟨1, a⟩, ⟨1, b⟩, Sum.Lex.inr H => Sigma.Lex.right _ _ H,
      λH => match a, b, H with
      | ⟨0, a⟩, ⟨0, b⟩, Sigma.Lex.right _ _ H => Sum.Lex.inl H
      | ⟨0, a⟩, ⟨1, b⟩, _ => Sum.Lex.sep _ _
      | ⟨1, a⟩, ⟨0, b⟩, Sigma.Lex.left _ _ H => by cases H
      | ⟨1, a⟩, ⟨1, b⟩, Sigma.Lex.right _ _ H => Sum.Lex.inr H
    ⟩,
    action_eq := λ{a} => 
      match a with | ⟨0, a⟩ => rfl | ⟨1, a⟩ => rfl
  }

def PomIso.par_ord {L} {N M} [PartialOrder N] [PartialOrder M] (α: N ⊕ M -> Pom L)
  : PomIso (Pom.sigma α) ((Pom.sigma (α ∘ Sum.inl)).par (Pom.sigma (α ∘ Sum.inr)))
  := sorry

def PomIso.par_elim {L} {N M} [PartialOrder N] [PartialOrder M] (α: N -> Pom L) (β: M -> Pom L)
  : PomIso ((Pom.sigma α).par (Pom.sigma β)) (Pom.sigma (Sum.elim α β))
  := sorry

def PomIso.par2 {L} (α: Unit ⊕ Unit -> Pom L): PomIso (Pom.sigma α) ((α (Sum.inl ())).par (α (Sum.inr ()))) := sorry