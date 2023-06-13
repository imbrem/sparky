import Mathlib.Init.Algebra.Order
import Mathlib.Order.RelIso.Basic
import Mathlib.Order.Synonym
import Mathlib.Data.Set.Finite
import Mathlib.Data.Sigma.Order
import Mathlib.Data.Sum.Order
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Relation

open Classical

structure Pom (L: Type) :=
  carrier: Type
  order: PartialOrder carrier
  action: carrier -> L

instance {L}: CoeOut (Pom L) (Type) := {
  coe := Pom.carrier
}

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

def PomIso.symm_toRelIso {L} {α β: Pom L} (φ: PomIso α β): φ.symm.toRelIso = φ.toRelIso.symm 
  := rfl
def PomIso.symm_toEquiv {L} {α β: Pom L} (φ: PomIso α β): φ.symm.toEquiv = φ.toEquiv.symm 
  := rfl

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
    action_eq := λ{e} => 
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
    action_eq := λ{e} => by 
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

def SubPom.iso_univ {L} (α: Pom L): PomIso (SubPom.univ α) α
  := {
    toFun := λ⟨e, _⟩ => e,
    invFun := λe => ⟨e, True.intro⟩,
    left_inv := λ_ => rfl,
    right_inv := λ_ => rfl,
    map_rel_iff' := Iff.rfl,
    action_eq := rfl
  }

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

theorem SubPom.order_char {L} {α: Pom L} {ρ: SubPom α}
  (a b: ρ.carrier)
  : ρ.order.le a b ↔ α.order.le a.val b.val
  := by rfl

theorem SubPom.order_char' {L} {α: Pom L} {ρ: SubPom α}
  (a b: ρ.carrier)
  : ρ.toPom.order.le a b ↔ α.order.le a.val b.val
  := by rfl

structure PomReduct {L} [Ticked L] (α: Pom L) :=
  shared: SubPom α
  is_reduct: PomReduces shared

instance {L} [Ticked L] {α: Pom L}: Coe (PomReduct α) (SubPom α) := {
  coe := PomReduct.shared
}

instance {L} [Ticked L] {α: Pom L}: CoeOut (PomReduct α) (Pom L) := {
  coe := λe => e.shared.toPom
}

def PomReduct.univ {L} [Ticked L] (α: Pom L): PomReduct α := {
  shared := SubPom.univ α
  is_reduct := PomReduces.refl α
}

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
  shared: Pom L
  reduce_left: PomReduct shared
  reduce_right: PomReduct shared
  iso_left: PomIso reduce_left α
  iso_right: PomIso reduce_right β

def PomEquiv.refl {L} [Ticked L] (α: Pom L): PomEquiv α α := {
  shared := α,
  reduce_left := PomReduct.univ α,
  reduce_right := PomReduct.univ α,
  iso_left := SubPom.iso_univ α,
  iso_right := SubPom.iso_univ α
}

def PomEquiv.symm {L} [Ticked L] {α β: Pom L} (P: PomEquiv α β): PomEquiv β α := {
  shared := P.shared,
  reduce_left := P.reduce_right,
  reduce_right := P.reduce_left,
  iso_left := P.iso_right,
  iso_right := P.iso_left
}

def PomEquiv.left_rem {L} [Ticked L] {α β: Pom L} (P: PomEquiv α β): SubPom P.shared
  := (P.reduce_left.shared.deletion P.reduce_right.shared)

def PomEquiv.right_rem {L} [Ticked L] {α β: Pom L} (P: PomEquiv α β): SubPom P.shared
  := (P.reduce_right.shared.deletion P.reduce_left.shared)

def PomEquiv.trans_carrier {L} [Ticked L] {α β γ: Pom L} 
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  : Type
  := β.carrier ⊕ (P.left_rem ⊕ Q.right_rem)

def PomEquiv.trans_le {L} [Ticked L] {α β γ: Pom L} 
  {P: PomEquiv α β} {Q: PomEquiv β γ}
  : P.trans_carrier Q ->  P.trans_carrier Q -> Prop
  | Sum.inl l, Sum.inl r => β.order.le l r
  | Sum.inl l, Sum.inr (Sum.inl r) => P.shared.order.le (P.iso_right.invFun l).val r.val
  | Sum.inl l, Sum.inr (Sum.inr r) => Q.shared.order.le (Q.iso_left.invFun l).val r.val
  | Sum.inr (Sum.inl l), Sum.inl r => P.shared.order.le l.val (P.iso_right.invFun r).val
  | Sum.inr (Sum.inl l), Sum.inr (Sum.inl r) => P.shared.order.le l.val r.val
  | Sum.inr (Sum.inl l), Sum.inr (Sum.inr r) => 
    ∃b: β.carrier, 
      P.shared.order.le l.val (P.iso_right.invFun b).val ∧
      Q.shared.order.le (Q.iso_left.invFun b).val r.val
  | Sum.inr (Sum.inr l), Sum.inl r => Q.shared.order.le l.val (Q.iso_left.invFun r).val
  | Sum.inr (Sum.inr l), Sum.inr (Sum.inl r) => 
    ∃b: β.carrier, 
      Q.shared.order.le l.val (Q.iso_left.invFun b).val ∧
      P.shared.order.le (P.iso_right.invFun b).val r.val
  | Sum.inr (Sum.inr l), Sum.inr (Sum.inr r) => Q.shared.order.le l.val r.val

def PomEquiv.trans_order {L} [Ticked L] {α β γ: Pom L} (P: PomEquiv α β) (Q: PomEquiv β γ)
  : PartialOrder (P.trans_carrier Q)
  := {
    le := trans_le,
    le_refl := λe => match e with
    | Sum.inl e => β.order.le_refl e
    | Sum.inr (Sum.inl e) => P.shared.order.le_refl e.val
    | Sum.inr (Sum.inr e) => Q.shared.order.le_refl e.val,
    le_trans := λx y z Hxy Hyz => 
      match x, y, z with
      | Sum.inl _xb, Sum.inl _yb, Sum.inl _zb => 
        β.order.le_trans _ _ _ Hxy Hyz
      | Sum.inl _xb, Sum.inl _yb, Sum.inr (Sum.inl _za) =>
        P.shared.order.le_trans _ _ _ (P.iso_right.symm.map_rel_iff.mpr Hxy) Hyz
      | Sum.inl _xb, Sum.inl _yb, Sum.inr (Sum.inr _zc) => 
        Q.shared.order.le_trans _ _ _ (Q.iso_left.symm.map_rel_iff.mpr Hxy) Hyz
      | Sum.inl _xb, Sum.inr (Sum.inl _ya), Sum.inl _zb =>   
        P.iso_right.symm.map_rel_iff.mp (P.shared.order.le_trans _ _ _ Hxy Hyz)
      | Sum.inl _xb, Sum.inr (Sum.inl _ya), Sum.inr (Sum.inl _za) => 
        P.shared.order.le_trans _ _ _ Hxy Hyz
      | Sum.inl xb, Sum.inr (Sum.inl ya), Sum.inr (Sum.inr zc) => 
        match Hyz with
        | ⟨qb, Hyq, Hqz⟩ =>
          Q.shared.order.le_trans _ _ _ 
            (Q.iso_left.map_rel_iff.mp (P.iso_right.symm.map_rel_iff.mp (
              P.shared.order.le_trans _ _ _ 
              ((RelIso.apply_symm_apply Q.iso_left.toRelIso xb).symm ▸ Hxy) 
              ((RelIso.apply_symm_apply Q.iso_left.toRelIso qb).symm ▸ Hyq)
            ))) 
            Hqz
      | Sum.inl _xb, Sum.inr (Sum.inr _yc), Sum.inl _zb => 
        Q.iso_left.symm.map_rel_iff.mp (Q.shared.order.le_trans _ _ _ Hxy Hyz)
      | Sum.inl xb, Sum.inr (Sum.inr _yc), Sum.inr (Sum.inl _za) => 
        match Hyz with
        | ⟨qb, Hyq, Hqz⟩ =>
            P.shared.order.le_trans _ _ _ 
              (P.iso_right.map_rel_iff.mp (Q.iso_left.symm.map_rel_iff.mp 
              (
                Q.shared.order.le_trans _ _ _ 
                ((RelIso.apply_symm_apply P.iso_right.toRelIso xb).symm ▸ Hxy) 
                ((RelIso.apply_symm_apply P.iso_right.toRelIso qb).symm ▸ Hyq)
              )))
              Hqz
      | Sum.inl _xb, Sum.inr (Sum.inr _yc), Sum.inr (Sum.inr _zc) => 
        Q.shared.order.le_trans _ _ _ Hxy Hyz
      | Sum.inr (Sum.inl _xa), Sum.inl _yb, Sum.inl _zb => 
        P.shared.order.le_trans _ _ _ Hxy (P.iso_right.symm.map_rel_iff.mpr Hyz)
      | Sum.inr (Sum.inl _xa), Sum.inl _yb, Sum.inr (Sum.inl _za) => 
        P.shared.order.le_trans _ _ _ Hxy Hyz
      | Sum.inr (Sum.inl _xa), Sum.inl yb, Sum.inr (Sum.inr _zc) => ⟨yb, Hxy, Hyz⟩
      | Sum.inr (Sum.inl _xa), Sum.inr (Sum.inl _ya), Sum.inl _zb => 
        P.shared.order.le_trans _ _ _ Hxy Hyz
      | Sum.inr (Sum.inl _xa), Sum.inr (Sum.inl _ya), Sum.inr (Sum.inl _za) => 
        P.shared.order.le_trans _ _ _ Hxy Hyz
      | Sum.inr (Sum.inl _xa), Sum.inr (Sum.inl _ya), Sum.inr (Sum.inr _zc) => 
        match Hyz with
        | ⟨qb, Hyq, Hqz⟩ => ⟨qb, P.shared.order.le_trans _ _ _ Hxy Hyq, Hqz⟩
      | Sum.inr (Sum.inl _xa), Sum.inr (Sum.inr _yc), Sum.inl zb => 
        match Hxy with
        | ⟨qb, Hxq, Hqy⟩ => P.shared.order.le_trans _ _ _ Hxq 
          (P.iso_right.map_rel_iff.mp (Q.iso_left.symm.map_rel_iff.mp (
              Q.shared.order.le_trans _ _ _
              ((RelIso.apply_symm_apply P.iso_right.toRelIso qb).symm ▸ Hqy)
              ((RelIso.apply_symm_apply P.iso_right.toRelIso zb).symm ▸ Hyz)
            )
          ))
      | Sum.inr (Sum.inl _xa), Sum.inr (Sum.inr _yc), Sum.inr (Sum.inl _za) => 
        match Hxy, Hyz with
        | ⟨qb, Hxq, Hqy⟩, ⟨rb, Hyr, Hrz⟩ => 
           P.shared.order.le_trans _ _ _ Hxq
            (P.shared.order.le_trans _ _ _ (
              P.iso_right.map_rel_iff.mp (Q.iso_left.symm.map_rel_iff.mp (
                Q.shared.order.le_trans _ _ _ 
                  ((RelIso.apply_symm_apply P.iso_right.toRelIso qb).symm ▸ Hqy) 
                  ((RelIso.apply_symm_apply P.iso_right.toRelIso rb).symm ▸ Hyr)
              ))
            ) Hrz)
      | Sum.inr (Sum.inl _xa), Sum.inr (Sum.inr _yc), Sum.inr (Sum.inr _zc) => 
        match Hxy with
        | ⟨qb, Hxq, Hqy⟩ => ⟨qb, Hxq, Q.shared.order.le_trans _ _ _ Hqy Hyz⟩
      | Sum.inr (Sum.inr _xc), Sum.inl _yb, Sum.inl _zb => 
        Q.shared.order.le_trans _ _ _ Hxy (Q.iso_left.symm.map_rel_iff.mpr Hyz)
      | Sum.inr (Sum.inr _xc), Sum.inl yb, Sum.inr (Sum.inl _za) => ⟨yb, Hxy, Hyz⟩
      | Sum.inr (Sum.inr _xc), Sum.inl _yb, Sum.inr (Sum.inr _zc) => 
        Q.shared.order.le_trans _ _ _ Hxy Hyz
      | Sum.inr (Sum.inr _xc), Sum.inr (Sum.inl _ya), Sum.inl zb => 
        match Hxy with
        | ⟨qb, Hxq, Hqy⟩ => Q.shared.order.le_trans _ _ _ Hxq 
          (Q.iso_left.map_rel_iff.mp (P.iso_right.symm.map_rel_iff.mp (
            P.shared.order.le_trans _ _ _
            ((RelIso.apply_symm_apply Q.iso_left.toRelIso qb).symm ▸ Hqy)
            ((RelIso.apply_symm_apply Q.iso_left.toRelIso zb).symm ▸ Hyz)
          )
          ))
      | Sum.inr (Sum.inr _xc), Sum.inr (Sum.inl _ya), Sum.inr (Sum.inl _za) => 
        match Hxy with
        | ⟨qb, Hxq, Hqy⟩ => ⟨qb, Hxq, P.shared.order.le_trans _ _ _ Hqy Hyz⟩
      | Sum.inr (Sum.inr _xc), Sum.inr (Sum.inl _ya), Sum.inr (Sum.inr _zc) => 
        match Hxy, Hyz with
        | ⟨qb, Hxq, Hqy⟩, ⟨rb, Hyr, Hrz⟩ => 
           Q.shared.order.le_trans _ _ _ Hxq
            (Q.shared.order.le_trans _ _ _ (
              Q.iso_left.map_rel_iff.mp (P.iso_right.symm.map_rel_iff.mp (
                P.shared.order.le_trans _ _ _ 
                  ((RelIso.apply_symm_apply Q.iso_left.toRelIso qb).symm ▸ Hqy) 
                  ((RelIso.apply_symm_apply Q.iso_left.toRelIso rb).symm ▸ Hyr)
              ))
            ) Hrz)
      | Sum.inr (Sum.inr _xc), Sum.inr (Sum.inr _yc), Sum.inl _zb => 
        Q.shared.order.le_trans _ _ _ Hxy Hyz
      | Sum.inr (Sum.inr _xc), Sum.inr (Sum.inr _yc), Sum.inr (Sum.inl _za) => 
        match Hyz with
        | ⟨qb, Hyq, Hqz⟩ => ⟨qb, Q.shared.order.le_trans _ _ _ Hxy Hyq, Hqz⟩
      | Sum.inr (Sum.inr _xc), Sum.inr (Sum.inr _yc), Sum.inr (Sum.inr _zc) => 
        Q.shared.order.le_trans _ _ _ Hxy Hyz
      ,
    le_antisymm := λa b =>
      match a, b with
      | Sum.inl a, Sum.inl b => 
        λHab Hba => by rw [β.order.le_antisymm a b Hab Hba]
      | Sum.inl a, Sum.inr (Sum.inl ⟨b, ⟨Hbl, Hbr⟩⟩) =>
        λHab Hba => by {
          apply False.elim;
          apply Hbr;
          simp [<-P.shared.order.le_antisymm _ b Hab Hba]
        }
      | Sum.inl a, Sum.inr (Sum.inr ⟨b, ⟨Hbl, Hbr⟩⟩) =>
        λHab Hba => by {
          apply False.elim;
          apply Hbr;
          simp [<-Q.shared.order.le_antisymm _ b Hab Hba]
        }
      | Sum.inr (Sum.inl ⟨a, ⟨Hal, Har⟩⟩), Sum.inl b =>
        λHab Hba => by {
          apply False.elim;
          apply Har;
          simp [P.shared.order.le_antisymm a _ Hab Hba]
        }
      | Sum.inr (Sum.inl ⟨a, _⟩), Sum.inr (Sum.inl ⟨b, _⟩) => 
        λHab Hba => by simp [P.shared.order.le_antisymm a b Hab Hba]
      | Sum.inr (Sum.inl ⟨a, ⟨Hal, Har⟩⟩), Sum.inr (Sum.inr ⟨b, ⟨Hbl, Hbr⟩⟩) =>
        λHab Hba => by {
          cases Hab with | intro q Hab => cases Hba with | intro s Hba =>
          cases Hab with | intro Haq Hqb => cases Hba with | intro Hbs Hsa =>
            have Hsq: s = q :=
              β.order.le_antisymm s q 
              (P.iso_right.symm.map_rel_iff.mp 
                (P.shared.order.le_trans _ _ _ Hsa Haq))
              (Q.iso_left.symm.map_rel_iff.mp 
                (Q.shared.order.le_trans _ _ _ Hqb Hbs))
              ;
            apply False.elim;
            apply Har;
            simp [P.shared.order.le_antisymm a _ Haq (Hsq ▸ Hsa)]
        } 
      | Sum.inr (Sum.inr ⟨a, ⟨Hal, Har⟩⟩), Sum.inl b =>
        λHab Hba => by {
          apply False.elim;
          apply Har;
          simp [Q.shared.order.le_antisymm a _ Hab Hba]
        }
      | Sum.inr (Sum.inr ⟨a, ⟨Hal, Har⟩⟩), Sum.inr (Sum.inl ⟨b, ⟨Hbl, Hbr⟩⟩) => 
        λHab Hba => by {
          cases Hab with | intro q Hab => cases Hba with | intro s Hba =>
          cases Hab with | intro Haq Hqb => cases Hba with | intro Hbs Hsa =>
            have Hsq: s = q :=
              β.order.le_antisymm s q 
              (Q.iso_left.symm.map_rel_iff.mp 
                (Q.shared.order.le_trans _ _ _ Hsa Haq))
              (P.iso_right.symm.map_rel_iff.mp 
                (P.shared.order.le_trans _ _ _ Hqb Hbs))
              ;
            apply False.elim;
            apply Hbr;
            have Hb' := P.shared.order.le_antisymm _ _ Hbs (Hsq.symm ▸ Hqb);
            simp at *
            simp [Hb']
        } 
      | Sum.inr (Sum.inr ⟨a, _⟩), Sum.inr (Sum.inr ⟨b, _⟩) =>
        λHab Hba => by simp [Q.shared.order.le_antisymm a b Hab Hba]
  }

def PomEquiv.trans_action {L} [Ticked L] {α β γ: Pom L} 
  {P: PomEquiv α β} {Q: PomEquiv β γ}
  : P.trans_carrier Q -> L
  | Sum.inl b => β.action b
  | Sum.inr (Sum.inl p) => P.shared.action p.val
  | Sum.inr (Sum.inr q) => Q.shared.action q.val

def PomEquiv.trans_pom {L} [Ticked L] {α β γ: Pom L} 
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  : Pom L
  := {
    carrier := P.trans_carrier Q,
    order := P.trans_order Q,
    action := trans_action
  }

theorem PomEquiv.trans_order_mid {L} [Ticked L] {α β γ: Pom L}
  {P: PomEquiv α β} {Q: PomEquiv β γ}
  (a b: β.carrier)
  :  (P.trans_pom Q).order.le (Sum.inl a) (Sum.inl b) ↔ β.order.le a b
  := by rfl

theorem PomEquiv.trans_order_left {L} [Ticked L] {α β γ: Pom L}
  {P: PomEquiv α β} {Q: PomEquiv β γ}
  (a b: P.left_rem.carrier)
  :  (P.trans_pom Q).order.le (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inl b)) 
    ↔ P.left_rem.order.le a b
  := by rfl

theorem PomEquiv.trans_order_left_mid {L} [Ticked L] {α β γ: Pom L}
  {P: PomEquiv α β} {Q: PomEquiv β γ}
  (a: P.left_rem.carrier) (b: β.carrier)
  :  (P.trans_pom Q).order.le (Sum.inr (Sum.inl a)) (Sum.inl b) 
    ↔ P.shared.order.le a.val (P.iso_right.invFun b).val
  := by rfl

theorem PomEquiv.trans_order_mid_left {L} [Ticked L] {α β γ: Pom L}
  {P: PomEquiv α β} {Q: PomEquiv β γ}
  (b: β.carrier) (a: P.left_rem.carrier)
  :  (P.trans_pom Q).order.le (Sum.inl b) (Sum.inr (Sum.inl a))
    ↔ P.shared.order.le (P.iso_right.invFun b).val a.val
  := by rfl

theorem PomEquiv.trans_order_right {L} [Ticked L] {α β γ: Pom L}
  {P: PomEquiv α β} {Q: PomEquiv β γ}
  (a b: Q.right_rem.carrier)
  :  (P.trans_pom Q).order.le (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inr b)) 
    ↔ Q.right_rem.order.le a b
  := by rfl

theorem PomEquiv.trans_order_right_mid {L} [Ticked L] {α β γ: Pom L}
  {P: PomEquiv α β} {Q: PomEquiv β γ}
  (a: Q.right_rem.carrier) (b: β.carrier)
  :  (P.trans_pom Q).order.le (Sum.inr (Sum.inr a)) (Sum.inl b) 
    ↔ Q.shared.order.le a.val (Q.iso_left.invFun b).val
  := by rfl

theorem PomEquiv.trans_order_mid_right {L} [Ticked L] {α β γ: Pom L}
  {P: PomEquiv α β} {Q: PomEquiv β γ}
  (b: β.carrier) (a: Q.right_rem.carrier)
  :  (P.trans_pom Q).order.le (Sum.inl b) (Sum.inr (Sum.inr a))
    ↔ Q.shared.order.le (Q.iso_left.invFun b).val a.val
  := by rfl

def PomEquiv.trans_sub_left_pom {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  : SubPom (P.trans_pom Q)
  := ⟨ 
    λe => match e with
    | Sum.inl _ | Sum.inr (Sum.inl _) => True
    | _ => False 
  ⟩ 

def PomEquiv.trans_sub_right_pom {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  : SubPom (P.trans_pom Q)
  := ⟨
    λe => match e with
    | Sum.inl _ | Sum.inr (Sum.inr _) => True
    | _ => False 
  ⟩

def PomEquiv.trans_sub_src_pom {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  : SubPom (P.trans_pom Q)
  := ⟨
    λe => match e with
    | Sum.inl b => (P.iso_right.invFun b).val ∈ P.reduce_left.shared.contains
    | Sum.inr (Sum.inl _) => True
    | _ => False 
  ⟩

def PomEquiv.trans_sub_tar_pom {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  : SubPom (P.trans_pom Q)
  := ⟨
    λe => match e with
    | Sum.inl b => (Q.iso_left.invFun b).val ∈ Q.reduce_right.shared.contains
    | Sum.inr (Sum.inr _) => True
    | _ => False 
  ⟩

theorem PomEquiv.left_iso_self {L} [Ticked L] {α β: Pom L} (P: PomEquiv α β)
  (p: (SubPom.toPom P.reduce_left.shared).carrier)
  : P.iso_left.toRelIso.invFun (P.iso_left.toRelIso.toFun p) = p
  := Equiv.symm_apply_apply _ p

theorem PomEquiv.right_iso_self {L} [Ticked L] {α β: Pom L} (P: PomEquiv α β)
  (p: (SubPom.toPom P.reduce_right.shared).carrier)
  : P.iso_right.toRelIso.invFun (P.iso_right.toRelIso.toFun p) = p
  := Equiv.symm_apply_apply _ p

def PomEquiv.trans_src_toFun {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  (e: (P.trans_sub_src_pom Q).carrier): α.carrier
  := match e with
      | ⟨Sum.inl e, p⟩ => 
        P.iso_left.toFun ⟨(P.iso_right.invFun e).val, p⟩ 
      | ⟨Sum.inr (Sum.inl e), _⟩ => 
        P.iso_left.toFun ⟨e.val, e.property.left⟩ 
      | ⟨Sum.inr (Sum.inr _), p⟩ => match p with.

theorem PomEquiv.trans_src_toFun_mid {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ) (e: β.carrier) (p)
  : P.trans_src_toFun Q ⟨Sum.inl e, p⟩  = P.iso_left.toFun ⟨(P.iso_right.invFun e).val, p⟩ 
  := rfl

theorem PomEquiv.trans_src_toFun_left {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ) (e: P.left_rem.carrier) (p)
  : P.trans_src_toFun Q ⟨Sum.inr (Sum.inl e), p⟩ = P.iso_left.toFun ⟨e.val, e.property.left⟩ 
  := rfl

noncomputable def PomEquiv.trans_src_invFun {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  (e: α.carrier): (P.trans_sub_src_pom Q).carrier
  := let ⟨e, He⟩ := P.iso_left.invFun e;
        if p: e ∈ P.reduce_right.shared.contains
        then 
          ⟨Sum.inl (P.iso_right.toFun ⟨e, p⟩), by {
            simp [
              trans_sub_src_pom, 
              Membership.mem, 
              Set.Mem
            ]
            exact (RelIso.symm_apply_apply P.iso_right.toRelIso ⟨e, p⟩).symm ▸ He
          }⟩
        else 
          ⟨Sum.inr (Sum.inl ⟨e, He, p⟩), True.intro⟩

theorem PomEquiv.trans_src_left_inv [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  : Function.LeftInverse (P.trans_src_invFun Q) (P.trans_src_toFun Q)
  := λ⟨e, _⟩ => match e with
    | Sum.inl e => by {
      rw [trans_src_toFun, trans_src_invFun]
      simp only []
      rw [P.left_iso_self]
      simp only []
      split
      case inl H => simp
      case inr H' => 
        apply False.elim;
        apply H';
        simp
    }
    | Sum.inr (Sum.inl ⟨e, He, Hr⟩) => by {
      rw [trans_src_toFun, trans_src_invFun]
      simp only []
      rw [P.left_iso_self]
      simp only []
      split
      case inl H => exact (Hr H).elim
      case inr H => simp
    }

theorem PomEquiv.trans_src_right_inv [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  : Function.RightInverse (P.trans_src_invFun Q) (P.trans_src_toFun Q)
  := λe => by {
        rw [trans_src_toFun, trans_src_invFun]
        simp only [Equiv.invFun_as_coe, Equiv.toFun_as_coe]
        generalize He: P.iso_left.toEquiv.symm e = e';
        cases e' with
        | mk e' He' =>
          simp only []
          let Pr := e' ∈ P.reduce_right.shared.contains;
          cases Classical.em Pr with
          | inl H =>
            simp only [H]
            apply P.iso_left.symm.injective;
            rw [<-RelIso.coe_toEquiv]
            rw [PomIso.symm_toEquiv]
            rw [He]
            rw [P.iso_left.left_inv']
            apply Subtype.eq
            simp only []
            rw [P.iso_right.left_inv']
          | inr H => 
            simp [
              H, <-He, 
              <-PomIso.symm_toEquiv,
              PomIso.symm_toRelIso
            ]
      }

noncomputable def PomEquiv.trans_sub_src_iso {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  : PomIso (P.trans_sub_src_pom Q) α
  := {
      toFun := P.trans_src_toFun Q,
      invFun := P.trans_src_invFun Q,
      left_inv := P.trans_src_left_inv Q,
      right_inv := P.trans_src_right_inv Q,
      map_rel_iff' := λ{a b} =>
        match a, b with
        | ⟨Sum.inl _, _⟩, ⟨Sum.inl _, _⟩ => by
            simp [
              trans_src_toFun_mid, 
              P.iso_left.map_rel_iff
            ]
            apply P.iso_right.symm.map_rel_iff
        | ⟨Sum.inl _, _⟩, ⟨Sum.inr (Sum.inl _), _⟩ => by
            simp [
              trans_src_toFun_mid,
              trans_src_toFun_left,
              P.iso_left.map_rel_iff
            ]
            rfl
        | ⟨Sum.inr (Sum.inl _), _⟩, ⟨Sum.inl _, _⟩ => by
            simp [
              trans_src_toFun_mid,
              trans_src_toFun_left,
              P.iso_left.map_rel_iff
            ]
            rfl
        | ⟨Sum.inr (Sum.inl _), _⟩, ⟨Sum.inr (Sum.inl _), _⟩ => by
          simp [
            trans_src_toFun_left, 
            P.iso_left.map_rel_iff
          ]
          rfl
      ,
      action_eq := λ{a} =>
        match a with
        | ⟨Sum.inl a, Ha⟩ => by
          simp only [
            trans_pom, trans_action,
            SubPom.toPom, SubPom.action,
            P.iso_right.symm.action_eq,
            P.iso_left.symm.action_eq,
            PomIso.symm
          ]
          rw [trans_src_toFun_mid]
          simp
          rfl
        | ⟨Sum.inr (Sum.inl a), Ha⟩ => by
          simp only [
            trans_pom, trans_action,
            SubPom.toPom, SubPom.action,
            P.iso_left.symm.action_eq,
            PomIso.symm
          ]
          rw [trans_src_toFun_left]
          simp
    }

def PomEquiv.trans_tar_toFun {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  (e: (P.trans_sub_tar_pom Q).carrier): γ.carrier
  := match e with
      | ⟨Sum.inl e, p⟩ => 
        Q.iso_right.toFun ⟨(Q.iso_left.invFun e).val, p⟩ 
      | ⟨Sum.inr (Sum.inl _), p⟩ => match p with.
      | ⟨Sum.inr (Sum.inr e), _⟩ => 
        Q.iso_right.toFun ⟨e.val, e.property.left⟩ 

theorem PomEquiv.trans_tar_toFun_mid {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ) (e: β.carrier) (p)
  : P.trans_tar_toFun Q ⟨Sum.inl e, p⟩  = Q.iso_right.toFun ⟨(Q.iso_left.invFun e).val, p⟩ 
  := rfl

theorem PomEquiv.trans_tar_toFun_right {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ) (e: Q.right_rem.carrier) (p)
  : P.trans_tar_toFun Q ⟨Sum.inr (Sum.inr e), p⟩ = Q.iso_right.toFun ⟨e.val, e.property.left⟩ 
  := rfl

noncomputable def PomEquiv.trans_tar_invFun {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  (e: γ.carrier): (P.trans_sub_tar_pom Q).carrier
  := let ⟨e, He⟩ := Q.iso_right.invFun e;
        if p: e ∈ Q.reduce_left.shared.contains
        then 
          ⟨Sum.inl (Q.iso_left.toFun ⟨e, p⟩), by {
            simp [
              trans_sub_tar_pom, 
              Membership.mem, 
              Set.Mem
            ]
            exact (RelIso.symm_apply_apply Q.iso_left.toRelIso ⟨e, p⟩).symm ▸ He
          }⟩
        else 
          ⟨Sum.inr (Sum.inr ⟨e, He, p⟩), True.intro⟩

theorem PomEquiv.trans_tar_left_inv [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  : Function.LeftInverse (P.trans_tar_invFun Q) (P.trans_tar_toFun Q)
  := λ⟨e, _⟩ => match e with
    | Sum.inl e => by {
      rw [trans_tar_toFun, trans_tar_invFun]
      simp only []
      rw [Q.right_iso_self]
      simp only []
      split
      case inl H => simp
      case inr H' => 
        apply False.elim;
        apply H';
        simp
    }
    | Sum.inr (Sum.inr ⟨e, He, Hr⟩) => by {
      rw [trans_tar_toFun, trans_tar_invFun]
      simp only []
      rw [Q.right_iso_self]
      simp only []
      split
      case inl H => exact (Hr H).elim
      case inr H => simp
    }

theorem PomEquiv.trans_tar_right_inv [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  : Function.RightInverse (P.trans_tar_invFun Q) (P.trans_tar_toFun Q)
  := λe => by {
        rw [trans_tar_toFun, trans_tar_invFun]
        simp only [Equiv.invFun_as_coe, Equiv.toFun_as_coe]
        generalize He: Q.iso_right.toEquiv.symm e = e';
        cases e' with
        | mk e' He' =>
          simp only []
          let Pr := e' ∈ Q.reduce_left.shared.contains;
          cases Classical.em Pr with
          | inl H =>
            simp only [H]
            apply Q.iso_right.symm.injective;
            rw [<-RelIso.coe_toEquiv]
            rw [PomIso.symm_toEquiv]
            rw [He]
            rw [Q.iso_right.left_inv']
            apply Subtype.eq
            simp only []
            rw [Q.iso_left.left_inv']
          | inr H => 
            simp [
              H, <-He, 
              <-PomIso.symm_toEquiv,
              PomIso.symm_toRelIso
            ]
      }

noncomputable def PomEquiv.trans_sub_tar_iso {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  : PomIso (P.trans_sub_tar_pom Q) γ
  := {
      toFun := P.trans_tar_toFun Q,
      invFun := P.trans_tar_invFun Q,
      left_inv := P.trans_tar_left_inv Q,
      right_inv := P.trans_tar_right_inv Q,
      map_rel_iff' := λ{a b} =>
        match a, b with
        | ⟨Sum.inl _, _⟩, ⟨Sum.inl _, _⟩ => by
            simp [
              trans_tar_toFun_mid, 
              Q.iso_right.map_rel_iff
            ]
            apply Q.iso_left.symm.map_rel_iff
        | ⟨Sum.inl _, _⟩, ⟨Sum.inr (Sum.inr _), _⟩ => by
            simp [
              trans_tar_toFun_mid,
              trans_tar_toFun_right,
              Q.iso_right.map_rel_iff
            ]
            rfl
        | ⟨Sum.inr (Sum.inr _), _⟩, ⟨Sum.inl _, _⟩ => by
            simp [
              trans_tar_toFun_mid,
              trans_tar_toFun_right,
              Q.iso_right.map_rel_iff
            ]
            rfl
        | ⟨Sum.inr (Sum.inr _), _⟩, ⟨Sum.inr (Sum.inr _), _⟩ => by
          simp [
            trans_tar_toFun_right, 
            Q.iso_right.map_rel_iff
          ]
          rfl
      ,
      action_eq := λ{a} =>
        match a with
        | ⟨Sum.inl a, Ha⟩ => by
          simp only [
            trans_pom, trans_action,
            SubPom.toPom, SubPom.action,
            Q.iso_left.symm.action_eq,
            Q.iso_right.symm.action_eq,
            PomIso.symm
          ]
          rw [trans_tar_toFun_mid]
          simp
          rfl
        | ⟨Sum.inr (Sum.inr a), Ha⟩ => by
          simp only [
            trans_pom, trans_action,
            SubPom.toPom, SubPom.action,
            Q.iso_right.symm.action_eq,
            PomIso.symm
          ]
          rw [trans_tar_toFun_right]
          simp
    }

def PomEquiv.trans_sub_src {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  : PomReduct (P.trans_pom Q)
  := {
    shared := P.trans_sub_src_pom Q,
    is_reduct := {
      subset := λ_ _ => True.intro,
      infinite_or_tick := λ⟨p, _⟩ => 
        match p with
        | Sum.inl p =>  sorry
        | Sum.inr (Sum.inl p) => sorry
        | Sum.inr (Sum.inr p) => sorry,
      infinite_preserved := sorry,
      infinite_shared := sorry,
      empty_shared := sorry
    }
  }

def PomEquiv.trans_sub_tar {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  : PomReduct (P.trans_pom Q)
  := {
    shared := P.trans_sub_tar_pom Q,
    is_reduct := {
      subset := λ_ _ => True.intro,
      infinite_or_tick := sorry,
      infinite_preserved := sorry,
      infinite_shared := sorry,
      empty_shared := sorry
    }
  }

noncomputable def PomEquiv.trans {L} [Ticked L] {α β γ: Pom L} (P: PomEquiv α β) (Q: PomEquiv β γ)
  : PomEquiv α γ
  := {
    shared := P.trans_pom Q,
    reduce_left := P.trans_sub_src Q,
    reduce_right := P.trans_sub_tar Q,
    iso_left := P.trans_sub_src_iso Q,
    iso_right := P.trans_sub_tar_iso Q
  }