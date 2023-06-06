import Mathlib.Init.Algebra.Order
import Mathlib.Order.RelIso.Basic
import Mathlib.Order.Synonym
import Mathlib.Data.Sigma.Order
import Mathlib.Data.Sum.Order
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Set.Finite

open Classical

structure Pom (L: Type) :=
  carrier: Type
  order: PartialOrder carrier
  action: carrier -> L

instance {L}: CoeOut (Pom L) (Type) := {
  coe := Pom.carrier
}

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

def SubPom.univ {L} (α: Pom L): SubPom α := ⟨ Set.univ ⟩
def SubPom.empty {L} (α: Pom L): SubPom α := ⟨ ∅ ⟩ 
def SubPom.union {L} {α: Pom L} (ρ σ: SubPom α): SubPom α := 
   ⟨ ρ.contains ∪ σ.contains ⟩
def SubPom.inter {L} {α: Pom L} (ρ σ: SubPom α): SubPom α
  := ⟨ ρ.contains ∩ σ.contains ⟩ 
def SubPom.complement {L} {α: Pom L} (ρ: SubPom α): SubPom α 
  := ⟨ ρ.containsᶜ ⟩
def SubPom.deletion {L} {α: Pom L} (ρ σ: SubPom α): SubPom α
  := ⟨ ρ.contains ∩ σ.containsᶜ ⟩  

def SubPom.inter_comm {L} {α: Pom L} (ρ σ: SubPom α)
  : ρ.inter σ = σ.inter ρ
  := by simp [inter, Set.inter_comm]

def SubPom.inter_assoc {L} {α: Pom L} (ρ σ τ: SubPom α)
  : (ρ.inter σ).inter τ = ρ.inter (σ.inter τ)
  := by simp [inter, Set.inter_assoc]

def SubPom.union_comm {L} {α: Pom L} (ρ σ: SubPom α)
  : ρ.union σ = σ.union ρ
  := by simp [union, Set.union_comm]

def SubPom.inter_univ {L} {α: Pom L} (ρ: SubPom α)
  : ρ.inter (univ α) = ρ
  := by simp [inter, univ]

def SubPom.univ_inter {L} {α: Pom L} (ρ: SubPom α)
  : (univ α).inter ρ = ρ
  := by simp [inter, univ]

def SubPom.inter_self {L} {α: Pom L} (ρ: SubPom α)
  : ρ.inter ρ = ρ
  := by simp [inter]

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

theorem SubPom.contains_eq {L} {α: Pom L} {ρ σ: SubPom α} 
  (H: ρ.contains = σ.contains)
  : ρ = σ
  := by cases ρ; cases σ; cases H; rfl

instance {L} {α: Pom L}: CoeOut (SubPom α) (Pom L) := {
  coe := SubPom.toPom
}

instance {L} {α: Pom L}: CoeOut (SubPom α) (Type) := {
  coe := SubPom.carrier
}

def Pom.pred {L} (α: Pom L) (p: α.carrier): SubPom α
  := ⟨ α.order.le p ⟩

def SubPom.pred {L} {α: Pom L} (ρ: SubPom α) (p: ρ.carrier) 
  := ρ.inter (α.pred p.val)
def SubPom.happens {L} {α: Pom L} (ρ: SubPom α): SubPom α
  := ⟨ λe => ∃p: ρ.contains e, Finite (ρ.pred ⟨e, p⟩) ⟩ 
def SubPom.never {L} {α: Pom L} (ρ: SubPom α): SubPom α
  := ⟨ λe => ∃p: ρ.contains e, Finite (ρ.pred ⟨e, p⟩) ⟩
def SubPom.truncation {L} {α: Pom L} (ρ: SubPom α)
  := ρ.inter ρ.happens
def SubPom.t_inter {L} {α: Pom L} (ρ σ: SubPom α)
  := ρ.truncation.inter σ.truncation

def SubPom.univ_pred_pred_univ {L} (α: Pom L) (p)
  : (univ α).pred p = α.pred p.val
  := univ_inter (α.pred p.val)

theorem Pom.univ_carrier_equiv {L} (α: Pom L)
  : α.carrier ≃ (SubPom.univ α).carrier
  := ⟨
    λa => ⟨a, True.intro⟩,
    λ⟨a, True.intro⟩ => a,
    λ_ => rfl,
    λ⟨_, _⟩ => rfl
  ⟩

class Ticked (L: Type) :=
  δ: L

structure SubPomReduces {L} [Ticked L] {α: Pom L} (ρ σ: SubPom α): Prop :=
  subset: σ.contains ⊆ ρ.contains
  infinite_or_tick: ∀p: ρ.contains,
    σ.contains p ∨
    Infinite (ρ.pred p) ∨
    α.action p = Ticked.δ
  infinite_preserved: ∀p: σ.carrier,
    Infinite (ρ.pred ⟨p.val, subset p.property⟩) -> Infinite (σ.pred p)
  infinite_shared: Infinite ρ -> Infinite σ
  empty_shared: IsEmpty ρ -> IsEmpty σ  

def PomReduces {L} [Ticked L] {α: Pom L} (ρ: SubPom α) := SubPomReduces (SubPom.univ α) ρ

theorem SubPomReduces.refl {L} [Ticked L] {α: Pom L} (ρ: SubPom α):
  SubPomReduces ρ ρ
  := {
    subset := subset_rfl,
    infinite_or_tick := λ⟨_, H⟩ => Or.inl H,
    infinite_preserved := λ_ H => H,
    infinite_shared := λH => H,
    empty_shared := λH => H,
  }

theorem PomReduces.refl {L} [Ticked L] (α: Pom L): PomReduces (SubPom.univ α)
  := SubPomReduces.refl (SubPom.univ α)

theorem SubPomReduces.trans {L} [Ticked L] {α: Pom L} {ρ σ τ: SubPom α}
  (Hρσ: SubPomReduces ρ σ) (Hστ: SubPomReduces σ τ)
  : SubPomReduces ρ τ
  := {
    subset := subset_trans Hστ.subset Hρσ.subset,
    infinite_or_tick := λe => 
      match Hρσ.infinite_or_tick e with
      | Or.inl H => 
        match Hστ.infinite_or_tick ⟨e.val, H⟩ with
        | Or.inl H => Or.inl H
        | Or.inr (Or.inl I) => Or.inr (Or.inl (
          @Infinite.of_injective
          _ _ I
          (λ⟨e, ⟨Hc, Hp⟩ ⟩  => ⟨e, ⟨Hρσ.subset Hc, Hp⟩⟩)
          (λ⟨_, ⟨_, _⟩⟩ ⟨_, ⟨_, _⟩⟩ H => by cases H; rfl)
        ))
        | Or.inr (Or.inr H) => Or.inr (Or.inr H)
      | Or.inr H => Or.inr H,
    infinite_preserved := λe => 
      Hστ.infinite_preserved e ∘ Hρσ.infinite_preserved ⟨e.val, Hστ.subset e.property⟩,
    infinite_shared := Hστ.infinite_shared ∘ Hρσ.infinite_shared,
    empty_shared := Hστ.empty_shared ∘ Hρσ.empty_shared,
  }

theorem SubPomReduces.antisymm {L} [Ticked L] 
  {α: Pom L} {ρ σ: SubPom α}
  (H: SubPomReduces ρ σ) (H': SubPomReduces σ ρ)
  : ρ = σ
  := SubPom.contains_eq (subset_antisymm H'.subset H.subset)

-- theorem SubPomReduces.inter {L} [Ticked L]
--   {α: Pom L} {ρ σ τ: SubPom α}
--   (Hσ: SubPomReduces ρ σ) (Hτ: SubPomReduces ρ τ)
--   : SubPomReduces ρ (σ.t_inter τ)
--   := {
--     subset := by {
--       apply subset_trans
--       apply subset_trans
--       apply Set.inter_subset_left
--       apply Set.inter_subset_inter Hσ.subset Hτ.subset
--       rw [Set.inter_self]
--     },
--     infinite_or_tick := λe => 
--       match Hσ.infinite_or_tick e with
--       | Or.inl H => match Hτ.infinite_or_tick e with
--         | Or.inl H' => 
--           match finite_or_infinite (ρ.pred e) with
--           | Or.inl F =>   
--             Or.inl (
--               Set.mem_inter (Set.mem_inter H H') 
--               F
--             )
--           | Or.inr I => Or.inr (Or.inl I)
--         | Or.inr H' => Or.inr H'
--       | Or.inr H => Or.inr H,
--     infinite_preserved := λe H =>
--       sorry,
--     infinite_shared := sorry,
--     empty_shared := sorry
--   }

def SubPom.flatten {L} {α: Pom L} {ρ: SubPom α} 
  (σ: SubPom ρ.toPom)
  : SubPom α
  := ⟨λe => (p: ρ.contains e) -> σ.contains ⟨e, p⟩⟩

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
  := {
    reduce_left := sorry,
    reduce_right := sorry,
    iso := sorry
  }