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

def PomIso.par2 {L} (α: Unit ⊕ Unit -> Pom L)
  : PomIso (Pom.sigma α) ((α (Sum.inl ())).par (α (Sum.inr ()))) 
  := sorry

def PomIso.empty_left_unit_seq {L} (α: Pom L)
  : PomIso ((Pom.empty L).seq α) α
  := {
    toFun := λa => match a with | Sum.inr a => a
    invFun := Sum.inr,
    left_inv := λa => match a with | Sum.inr _ => rfl,
    right_inv := λ_ => rfl,
    map_rel_iff' := λ{a b} => match a, b with 
      | Sum.inr _, Sum.inr _ => ⟨
        Sum.Lex.inr,
        λH => match H with | Sum.Lex.inr H => H
      ⟩,
    action_eq := λ{a} => match a with | Sum.inr _ => rfl
  }

def PomIso.empty_right_unit_seq {L} (α: Pom L)
  : PomIso (α.seq (Pom.empty L)) α
  := {
    toFun := λa => match a with | Sum.inl a => a
    invFun := Sum.inl,
    left_inv := λa => match a with | Sum.inl _ => rfl,
    right_inv := λ_ => rfl,
    map_rel_iff' := λ{a b} => match a, b with 
      | Sum.inl _, Sum.inl _ => ⟨
        Sum.Lex.inl,
        λH => match H with | Sum.Lex.inl H => H
      ⟩,
    action_eq := λ{a} => match a with | Sum.inl _ => rfl
  }

def PomIso.nat_sigma {L} (F: PomFamily ℕ L)
  : PomIso F.toPom ((F 0).seq (Pom.sigma (λn => F (n + 1))))
  := {
    toFun := λa => 
      match a with | ⟨0, a⟩ => Sum.inl a | ⟨n + 1, a⟩ => Sum.inr ⟨n, a⟩,
    invFun := λa => 
      match a with | Sum.inl a => ⟨0, a⟩ | Sum.inr ⟨n, a⟩ => ⟨n + 1, a⟩,
    left_inv := λa => 
      match a with | ⟨0, _⟩ => rfl | ⟨_ + 1, _⟩ => rfl,
    right_inv := λa => 
      match a with | Sum.inl _ => rfl | Sum.inr ⟨_, _⟩ => rfl,
    map_rel_iff' := λ{a b} =>
      match a, b with
      | ⟨0, _⟩, ⟨0, _⟩ => ⟨
        λH => match H with | Sum.Lex.inl H => Sigma.Lex.right _ _ H,
        λH => match H with | Sigma.Lex.right _ _ H => Sum.Lex.inl H
      ⟩  
      | ⟨0, _⟩, ⟨_ + 1, _⟩ => ⟨
        λ_ => Sigma.Lex.left _ _ (by simp),
        λ_ => Sum.Lex.sep _ _
      ⟩  
      | ⟨_ + 1, _⟩, ⟨0, _⟩ => ⟨
        λH => match H with.,
        λH => match H with. 
      ⟩ 
      | ⟨_ + 1, w⟩, ⟨_ + 1, z⟩ => ⟨
        λH => match H with 
          | Sum.Lex.inr H => by
            cases H with
            | left _ _ H => exact Sigma.Lex.left _ _ (Nat.succ_le_succ H)
            | right x y H => cases H; exact Sigma.Lex.right _ _ H,
        λH => Sum.Lex.inr (by
          cases H with
          | left _ _ H => exact Sigma.Lex.left _ _ (Nat.le_of_succ_le_succ H)
          | right _ _ H => exact Sigma.Lex.right _ _ H)
      ⟩    
    action_eq := λ{a} =>
      match a with | ⟨0, _⟩ => rfl | ⟨_ + 1, _⟩ => rfl
  }