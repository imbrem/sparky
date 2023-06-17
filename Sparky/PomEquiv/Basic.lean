import Sparky.Pom
import Sparky.PomIso
import Sparky.SubPom
import Sparky.PomReduce

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

theorem PomEquiv.infinite_shared_left {L} [Ticked L] {α β: Pom L}
  (P: PomEquiv α β)
  : Infinite P.shared ↔ Infinite α
  := by rw [
    <-P.reduce_left.is_reduct.infinite_iff',
    P.iso_left.infinite_iff
  ]

theorem PomEquiv.infinite_shared_right {L} [Ticked L] {α β: Pom L}
  (P: PomEquiv α β)
  : Infinite P.shared ↔ Infinite β
  := by rw [
    <-P.reduce_right.is_reduct.infinite_iff',
    P.iso_right.infinite_iff
  ]

theorem PomEquiv.infinite_shared_left' {L} [Ticked L] {α β: Pom L}
  (P: PomEquiv α β)
  : Infinite (SubPom.univ P.shared) ↔ Infinite α
  := Iff.trans (SubPom.iso_univ P.shared).infinite_iff P.infinite_shared_left

theorem PomEquiv.infinite_shared_right' {L} [Ticked L] {α β: Pom L}
  (P: PomEquiv α β)
  : Infinite (SubPom.univ P.shared) ↔ Infinite β
  := Iff.trans (SubPom.iso_univ P.shared).infinite_iff P.infinite_shared_right

theorem PomEquiv.infinite_iff {L} [Ticked L] {α β: Pom L}
  (P: PomEquiv α β)
  : Infinite α ↔ Infinite β
  := Iff.trans P.infinite_shared_left.symm P.infinite_shared_right

theorem PomEquiv.empty_shared_left {L} [Ticked L] {α β: Pom L}
  (P: PomEquiv α β)
  : IsEmpty P.shared ↔ IsEmpty α
  := by rw [
    <-P.reduce_left.is_reduct.empty_iff',
    P.iso_left.empty_iff
  ]

theorem PomEquiv.empty_shared_right {L} [Ticked L] {α β: Pom L}
  (P: PomEquiv α β)
  : IsEmpty P.shared ↔ IsEmpty β
  := by rw [
    <-P.reduce_right.is_reduct.empty_iff',
    P.iso_right.empty_iff
  ]

theorem PomEquiv.empty_iff {L} [Ticked L] {α β: Pom L}
  (P: PomEquiv α β)
  : IsEmpty α ↔ IsEmpty β
  := by rw [<-P.empty_shared_left, <-P.empty_shared_right]

@[simp]
theorem PomEquiv.left_iso_self {L} [Ticked L] {α β: Pom L} (P: PomEquiv α β)
  (p: (SubPom.toPom P.reduce_left.shared).carrier)
  : P.iso_left.toRelIso.invFun (P.iso_left.toRelIso.toFun p) = p
  := Equiv.symm_apply_apply _ p

@[simp]
theorem PomEquiv.right_iso_self {L} [Ticked L] {α β: Pom L} (P: PomEquiv α β)
  (p: (SubPom.toPom P.reduce_right.shared).carrier)
  : P.iso_right.toRelIso.invFun (P.iso_right.toRelIso.toFun p) = p
  := Equiv.symm_apply_apply _ p

def PomEquiv.left_rem {L} [Ticked L] {α β: Pom L} (P: PomEquiv α β): SubPom P.shared
  := (P.reduce_left.shared.deletion P.reduce_right.shared)

def PomEquiv.right_rem {L} [Ticked L] {α β: Pom L} (P: PomEquiv α β): SubPom P.shared
  := (P.reduce_right.shared.deletion P.reduce_left.shared)

def PomEquiv.left_rem_char {L} [Ticked L] {α β: Pom L} 
  (P: PomEquiv α β) (p: P.shared.carrier) (Hp: p ∉ P.reduce_right.shared.contains)
  : Infinite ((SubPom.univ P.shared).pred ⟨p, True.intro⟩) ∨ P.shared.action p = Ticked.δ
  := match P.reduce_right.is_reduct.infinite_or_tick ⟨p, True.intro⟩ with
  | Or.inl H => (Hp H).elim
  | Or.inr H => H

def PomEquiv.right_rem_char {L} [Ticked L] {α β: Pom L} 
  (P: PomEquiv α β) (p: P.shared.carrier) (Hp: p ∉ P.reduce_left.shared.contains)
  : Infinite ((SubPom.univ P.shared).pred ⟨p, True.intro⟩) ∨ P.shared.action p = Ticked.δ
  := match P.reduce_left.is_reduct.infinite_or_tick ⟨p, True.intro⟩ with
  | Or.inl H => (Hp H).elim
  | Or.inr H => H

def PomEquiv.left_action_eq {L} [Ticked L] {α β: Pom L}
  (P: PomEquiv α β) (e: α.carrier)
  : P.shared.action (P.iso_left.invFun e).val = α.action e
  := by
    simp [P.iso_left.symm.action_eq]
    rfl

def PomEquiv.right_action_eq {L} [Ticked L] {α β: Pom L}
  (P: PomEquiv α β) (e: β.carrier)
  : P.shared.action (P.iso_right.invFun e).val = β.action e
  := by
    simp [P.iso_right.symm.action_eq]
    rfl

def PomEquiv.left_shared_pred {L} [Ticked L] {α β: Pom L}
  (P: PomEquiv α β) (e: α.carrier) (p: P.reduce_left.shared.carrier) 
  : α.order.le e (P.iso_left.toFun p) 
  ↔ P.reduce_left.shared.order.le (P.iso_left.invFun e) p 
  := sorry

def PomEquiv.right_shared_pred {L} [Ticked L] {α β: Pom L}
  (P: PomEquiv α β) (e: β.carrier) (p: P.reduce_right.shared.carrier) 
  : β.order.le e (P.iso_right.toFun p) 
  ↔ P.reduce_right.shared.order.le (P.iso_right.invFun e) p 
  := sorry

def PomEquiv.left_shared_pred' {L} [Ticked L] {α β: Pom L}
  (P: PomEquiv α β) (e: α.carrier) (p: P.shared.carrier) (Hp) 
  : α.order.le e (P.iso_left.toFun ⟨p, Hp⟩) 
  ↔ P.shared.order.le (P.iso_left.invFun e).val p
  := sorry

def PomEquiv.right_shared_pred' {L} [Ticked L] {α β: Pom L}
  (P: PomEquiv α β) (e: β.carrier) (p: P.shared.carrier) (Hp) 
  : β.order.le e (P.iso_right.toFun ⟨p, Hp⟩) 
  ↔ P.shared.order.le (P.iso_right.invFun e).val p 
  := sorry