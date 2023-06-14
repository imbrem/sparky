import Sparky.Pom
import Sparky.PomIso

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

def Pom.pred_carrier {L} (α: Pom L) (p: α.carrier):
  α.pred p = (SubPom.univ α).pred ⟨p, True.intro⟩
  := by simp [SubPom.pred, SubPom.inter, SubPom.univ]

def PomIso.pred {L} {α β: Pom L} (φ: PomIso α β) (p: α.carrier):
  PomIso (α.pred p) (β.pred (φ.toFun p)).toPom
  := {
    toFun := λ⟨e, He⟩ => ⟨φ.toFun e, φ.map_rel_iff.mpr He⟩,
    invFun := λ⟨e, He⟩ => ⟨
      φ.invFun e, by
        have He': e = φ.toFun (φ.invFun e) := by simp;
        rw [He'] at He;
        exact φ.map_rel_iff.mp He;
      ⟩,
    left_inv := λ⟨e, _⟩ => Subtype.eq (φ.left_inv e),
    right_inv := λ⟨e, _⟩ => Subtype.eq (φ.right_inv e),
    map_rel_iff' := λ{a b} => by
      cases a; cases b;
      exact φ.map_rel_iff',
    action_eq := λ{a} => by cases a; exact φ.action_eq
  }

theorem PomIso.pred_infinite_iff {L} {α β: Pom L} (φ: PomIso α β) (p: α.carrier):
  Infinite (α.pred p) ↔ Infinite (β.pred (φ.toFun p))
  := (φ.pred p).infinite_iff

theorem PomIso.pred_empty_iff {L} {α β: Pom L} (φ: PomIso α β) (p: α.carrier):
  IsEmpty (α.pred p) ↔ IsEmpty (β.pred (φ.toFun p))
  := (φ.pred p).empty_iff

def SubPom.pred_iso {L} {α: Pom L} (ρ: SubPom α) (p: ρ.carrier)
  : PomIso (ρ.toPom.pred p).toPom (ρ.pred p).toPom
  := {
    toFun := λ⟨e, He⟩ => ⟨e.val, ⟨e.property, He⟩⟩,
    invFun := λ⟨e, He⟩ => ⟨⟨e, He.left⟩, He.right⟩,
    left_inv := λ⟨⟨_, _⟩, _⟩ => rfl,
    right_inv := λ⟨_, _, _⟩ => rfl,
    map_rel_iff' := λ{a b} => by rfl,
    action_eq := λ{a} => rfl 
  }

def PomIso.pred_sub {L} {α: Pom L} {ρ σ: SubPom α} 
  (φ: PomIso ρ.toPom σ.toPom) (p: ρ.carrier):
  PomIso (ρ.pred p).toPom (σ.pred (φ.toFun p)).toPom
  := PomIso.trans (ρ.pred_iso _).symm (PomIso.trans (φ.pred _) (σ.pred_iso _))

theorem PomIso.pred_sub_infinite_iff {L} {α: Pom L} {ρ σ: SubPom α} 
  (φ: PomIso ρ.toPom σ.toPom) (p: ρ.carrier):
  Infinite (ρ.pred p) ↔ Infinite (σ.pred (φ.toFun p))
  := (φ.pred_sub p).infinite_iff

theorem PomIso.pred_sub_empty_iff {L} {α: Pom L} {ρ σ: SubPom α} 
  (φ: PomIso ρ.toPom σ.toPom) (p: ρ.carrier):
  IsEmpty (ρ.pred p) ↔ IsEmpty (σ.pred (φ.toFun p))
  := (φ.pred_sub p).empty_iff

-- def PomIso.pred_inv {L} {α β: Pom L} (φ: PomIso α β) (p: β.carrier):
--   PomIso (α.pred (φ.invFun p)) (β.pred p).toPom
--   := sorry

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