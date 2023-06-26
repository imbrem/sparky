import Sparky.PomReduce.Basic

def SubPomReduces.sigma
  {L} [Ticked L]
  {N} [PartialOrder N]
  {F: N -> Pom L}
  (S: (n: N) -> SubPom (F n))
  (R: (n: N) -> SubPom (F n))
  (H: ∀(n: N), SubPomReduces (S n) (R n))
  : SubPomReduces (SubPom.sigma S) (SubPom.sigma R)
  := {
    subset := λ⟨n, e⟩ Hs => (H n).subset Hs,
    infinite_or_tick := λ⟨⟨n, e⟩, Hs⟩ => match (H n).infinite_or_tick ⟨e, Hs⟩ with
    | Or.inl Hi => Or.inl Hi
    | Or.inr (Or.inl Hi) => Or.inr (Or.inl (
      @Infinite.of_injective _ _ Hi 
        (λ⟨p, Hsp, Hep⟩  => ⟨⟨n, p⟩, Hsp, Sigma.Lex.right _ _ Hep⟩) 
        (λ⟨_, _, _⟩ ⟨_, _, _⟩ H => by cases H; rfl)
    ))
    | Or.inr (Or.inr Hi) => Or.inr (Or.inr Hi)
    ,
    infinite_preserved := sorry,
    infinite_shared := sorry,
    empty_shared := λHe =>
      have He := (SubPom.sigma_empty _).mp He;
      (SubPom.sigma_empty _).mpr (λn => (H n).empty_shared (He n))
  }

def PomReduces.sigma
  {L} [Ticked L]
  {N} [PartialOrder N]
  {F: N -> Pom L}
  (S: (n: N) -> SubPom (F n))
  (H: ∀(n: N), PomReduces (S n))
  : PomReduces (SubPom.sigma S)
  := SubPomReduces.sigma (λn => SubPom.univ (F n)) S H

def PomReduct.sigma
  {L} [Ticked L]
  {N} [PartialOrder N]
  {F: N -> Pom L}
  (P: ∀(n: N), PomReduct (F n))
  : PomReduct (Pom.sigma F)
  := {
    shared := SubPom.sigma (λn => (P n).shared),
    is_reduct := PomReduces.sigma _ (λn => (P n).is_reduct)
  }