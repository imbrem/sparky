import Sparky.SubPom.Basic
open Classical

def SubPom.sigma {L} {N: Type} [PartialOrder N] 
  {F: N -> Pom L} (SF: (n: N) -> SubPom (F n))
  : SubPom (Pom.sigma F)
  := ⟨ λ⟨n, e⟩ => (SF n).contains e ⟩

def SubPom.sigma_true {L} {N: Type} [PartialOrder N]
  (F: N -> Pom L)
  : SubPom.sigma (λn: N => SubPom.univ (F n)) = SubPom.univ (Pom.sigma F)
  := rfl

def SubPom.sigma_iso {L} {N: Type} [PartialOrder N]
  {F: N -> Pom L} (SF: (n: N) -> SubPom (F n))
  : PomIso (SubPom.sigma SF) (Pom.sigma (λn => (SF n).toPom))
  := {
    toFun := λ⟨⟨n, e⟩, H⟩ => ⟨n, e, H⟩,
    invFun := λ⟨n, e, H⟩ => ⟨⟨n, e⟩, H⟩,
    left_inv := λ⟨⟨_, _⟩, _⟩ => rfl,
    right_inv := λ⟨_, _, _⟩ => rfl,
    map_rel_iff' := λ{A B} => match A, B with 
      | ⟨⟨_, _⟩, _⟩, ⟨⟨_, _⟩, _⟩ => ⟨ 
        λH => by
          cases H with
          | left x y Hi => exact Sigma.Lex.left _ _ Hi
          | right x y Hx => exact Sigma.Lex.right _ _ Hx 
        ,
        λH => by
          cases H with
          | left x y Hi => exact Sigma.Lex.left _ _ Hi
          | right x y Hx => exact Sigma.Lex.right _ _ Hx 
      ⟩,
    action_eq := rfl
  }

theorem SubPom.sigma_empty {L} {N: Type} [PartialOrder N]
  {F: N -> Pom L} (SF: (n: N) -> SubPom (F n))
  : IsEmpty (SubPom.sigma SF) ↔ ∀(n: N), IsEmpty (SF n)
  := ⟨
    λH n => IsEmpty.mk (λ⟨s, Hs⟩  => H.elim ⟨⟨n, s⟩, Hs⟩),
    λH => IsEmpty.mk (λ⟨⟨n, s⟩, Hs⟩ => (H n).elim ⟨s, Hs⟩)
  ⟩

def SubPom.sigma_nonempty {L} {N: Type} [PartialOrder N]
  {F: N -> Pom L} (SF: (n: N) -> SubPom (F n)): Set N
  := λn => Nonempty (SF n)

theorem SubPom.sigma_infinite {L} {N: Type} [PartialOrder N]
  {F: N -> Pom L} (SF: (n: N) -> SubPom (F n))
  : Infinite (SubPom.sigma SF) ↔ (
    Infinite (SubPom.sigma_nonempty SF) ∨
    ∃n, Infinite (SF n) 
  )
  := sorry

def SubPom.sigma_fun_to_pred {L} {N: Type} [PartialOrder N]
  {F: N -> Pom L} (SF: (n: N) -> SubPom (F n)) (p: (SubPom.sigma SF).carrier) (n: N)
  : SubPom (F n)
  :=
    let ⟨⟨ne, e⟩, He⟩ := p; 
    ⟨ if p: n = ne then p ▸ ((SF ne).pred ⟨e, He⟩).contains else if n ≤ ne then (SF n).contains else ∅ ⟩ 

theorem SubPom.sigma_pred {L} {N: Type} [PartialOrder N]
  {F: N -> Pom L} (SF: (n: N) -> SubPom (F n)) (p: (SubPom.sigma SF).carrier)
  : (SubPom.sigma SF).pred p = (SubPom.sigma (SubPom.sigma_fun_to_pred SF p))
  := sorry
