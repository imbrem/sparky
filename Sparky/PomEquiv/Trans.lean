import Sparky.Pom
import Sparky.PomIso
import Sparky.SubPom
import Sparky.PomReduce
import Sparky.PomEquiv.Basic
import Sparky.Utils

open Classical

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

def PomEquiv.trans_le_mid {L} [Ticked L] {α β γ: Pom L} 
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  (l r: β.carrier)
  : @trans_le L _ α β γ P Q (Sum.inl l) (Sum.inl r) ↔ β.order.le l r
  := by rfl

def PomEquiv.trans_le_left {L} [Ticked L] {α β γ: Pom L} 
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  (l) (r)
  : @trans_le L _ α β γ P Q (Sum.inr (Sum.inl l)) (Sum.inr (Sum.inl r)) 
  ↔ P.shared.order.le l.val r.val
  := by rfl

def PomEquiv.trans_le_right {L} [Ticked L] {α β γ: Pom L} 
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  (l) (r)
  : @trans_le L _ α β γ P Q (Sum.inr (Sum.inr l)) (Sum.inr (Sum.inr r)) 
  ↔ Q.shared.order.le l.val r.val
  := by rfl

def PomEquiv.trans_le_mid_left {L} [Ticked L] {α β γ: Pom L} 
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  (l: β.carrier) (r)
  : @trans_le L _ α β γ P Q (Sum.inl l) (Sum.inr (Sum.inl r)) 
  ↔ P.shared.order.le (P.iso_right.invFun l).val r.val
  := by rfl

def PomEquiv.trans_le_mid_right {L} [Ticked L] {α β γ: Pom L} 
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  (l: β.carrier) (r)
  : @trans_le L _ α β γ P Q (Sum.inl l) (Sum.inr (Sum.inr r)) 
  ↔ Q.shared.order.le (Q.iso_left.invFun l).val r.val
  := by rfl

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

def PomEquiv.trans_left_right_infinite {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  : Infinite α ↔ Infinite γ
  := Iff.trans P.infinite_iff Q.infinite_iff

def PomEquiv.trans_left_right_empty {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  : IsEmpty α ↔ IsEmpty γ
  := Iff.trans P.empty_iff Q.empty_iff

def PomEquiv.trans_pom_mid_infinite {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  : Infinite (P.trans_pom Q) ↔ Infinite β
  := ⟨
    λH => match infinite_sum.mp H with
    | Or.inl H => H
    | Or.inr H => match infinite_sum.mp H with
      | Or.inl H => P.infinite_shared_right.mp 
        (@Infinite.of_injective _ _ H (λp => p.val) 
          (λ⟨_, _⟩ ⟨_, _⟩ H => by cases H; rfl))
      | Or.inr H => Q.infinite_shared_left.mp 
        (@Infinite.of_injective _ _ H (λp => p.val) 
          (λ⟨_, _⟩ ⟨_, _⟩ H => by cases H; rfl)),
    λ_ => Sum.infinite_of_left
  ⟩

def PomEquiv.trans_pom_mid_empty {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  : IsEmpty (P.trans_pom Q) ↔ IsEmpty β
  := ⟨
    λH => IsEmpty.mk (λb => H.elim (Sum.inl b)),
    λH => isEmpty_sum.mpr ⟨H, isEmpty_sum.mpr ⟨
      @instIsEmptySubtype _ (
        P.reduce_right.is_reduct.empty_iff'.mp 
        (P.iso_right.empty_iff.mpr H)
      ) _, 
      @instIsEmptySubtype _ (
        Q.reduce_left.is_reduct.empty_iff'.mp 
        (Q.iso_left.empty_iff.mpr H)
      ) _
    ⟩⟩
  ⟩

def PomEquiv.trans_pom_left_infinite {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  : Infinite (P.trans_pom Q) ↔ Infinite α
  := Iff.trans (P.trans_pom_mid_infinite Q) P.infinite_iff.symm

def PomEquiv.trans_pom_right_infinite {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  : Infinite (P.trans_pom Q) ↔ Infinite γ
  := Iff.trans (P.trans_pom_mid_infinite Q) Q.infinite_iff

def PomEquiv.trans_pom_left_empty {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  : IsEmpty (P.trans_pom Q) ↔ IsEmpty α
  := Iff.trans (P.trans_pom_mid_empty Q) P.empty_iff.symm

def PomEquiv.trans_pom_right_empty {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  : IsEmpty (P.trans_pom Q) ↔ IsEmpty γ
  := Iff.trans (P.trans_pom_mid_empty Q) Q.empty_iff

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

def PomEquiv.trans_sub_mid_pom {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  : SubPom (P.trans_pom Q)
  := ⟨
    λe => match e with
    | Sum.inl _ => True
    | Sum.inr _ => False
  ⟩

def PomEquiv.trans_sub_left_rem_pom {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  : SubPom (P.trans_pom Q)
  := ⟨
    λe => match e with
    | Sum.inr (Sum.inl _) => True
    | _ => False
  ⟩

def PomEquiv.trans_sub_right_rem_pom {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  : SubPom (P.trans_pom Q)
  := ⟨
    λe => match e with
    | Sum.inr (Sum.inr _) => True
    | _ => False
  ⟩

def PomEquiv.trans_pom_pred_factor_toFun {L} [Ticked L] {α β γ: Pom L}
  {P: PomEquiv α β} {Q: PomEquiv β γ} 
  {p: (P.trans_pom Q).carrier} 
  (e: ((P.trans_pom Q).pred p).carrier)
  : 
    ((P.trans_sub_mid_pom Q).inter ((P.trans_pom Q).pred p)).carrier
    ⊕ ((P.trans_sub_left_rem_pom Q).inter ((P.trans_pom Q).pred p)).carrier
    ⊕ ((P.trans_sub_right_rem_pom Q).inter ((P.trans_pom Q).pred p)).carrier
  := match e with 
  | ⟨Sum.inl e, He⟩ => Sum.inl ⟨Sum.inl e, True.intro, He⟩
  | ⟨Sum.inr (Sum.inl e), He⟩ => 
    Sum.inr (Sum.inl ⟨Sum.inr (Sum.inl e), True.intro, He⟩)
  | ⟨Sum.inr (Sum.inr e), He⟩ => 
    Sum.inr (Sum.inr ⟨Sum.inr (Sum.inr e), True.intro, He⟩)

theorem PomEquiv.trans_pom_pred_factor_toFun_injective {L} [Ticked L] {α β γ: Pom L}
  {P: PomEquiv α β} {Q: PomEquiv β γ} 
  (p: (P.trans_pom Q).carrier) 
  : Function.Injective (@trans_pom_pred_factor_toFun L _ α β γ P Q p)
  := λ⟨a, Ha⟩ ⟨b, Hb⟩ _H => by -- Wonder why H is marked unused here...
    cases a <;> 
    rename_i a <;>
    (first | cases a | skip) <;>
    cases b <;>
    rename_i b <;>
    (first | cases b | skip) <;>
    cases _H <;> 
    rfl

def PomEquiv.trans_pom_pred_factor_infinite {L} [Ticked L] {α β γ: Pom L}
  {P: PomEquiv α β} {Q: PomEquiv β γ} 
  {p: (P.trans_pom Q).carrier} 
  (H: Infinite ((P.trans_pom Q).pred p))
  : 
    Infinite ((P.trans_sub_mid_pom Q).inter ((P.trans_pom Q).pred p)).carrier
    ∨ Infinite ((P.trans_sub_left_rem_pom Q).inter ((P.trans_pom Q).pred p)).carrier
    ∨ Infinite ((P.trans_sub_right_rem_pom Q).inter ((P.trans_pom Q).pred p)).carrier
  :=
    have H := @Infinite.of_injective 
      _ _ H
      (trans_pom_pred_factor_toFun)
      (trans_pom_pred_factor_toFun_injective p);
    match infinite_sum.mp H with
    | Or.inl H => Or.inl H
    | Or.inr H => Or.inr (infinite_sum.mp H)

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
  : P.trans_tar_toFun Q ⟨Sum.inl e, p⟩ 
  = Q.iso_right.toFun ⟨(Q.iso_left.invFun e).val, p⟩ 
  := rfl

theorem PomEquiv.trans_tar_toFun_right {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ) (e: Q.right_rem.carrier) (p)
  : P.trans_tar_toFun Q ⟨Sum.inr (Sum.inr e), p⟩ 
  = Q.iso_right.toFun ⟨e.val, e.property.left⟩ 
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

-- theorem PomEquiv.trans_tar_invFun_eq_mid {L} [Ticked L] {α β γ: Pom L}
--   (P: PomEquiv α β) (Q: PomEquiv β γ) (b: β.carrier) (c: γ.carrier)
--   : Sum.inl b = (P.trans_tar_invFun Q c).val
--   ↔ (Q.iso_left.invFun b).val = (Q.iso_right.invFun c).val
--   := sorry

-- theorem PomEquiv.trans_tar_invFun_eq_right {L} [Ticked L] {α β γ: Pom L}
--   (P: PomEquiv α β) (Q: PomEquiv β γ) (r) (c: γ.carrier)
--   : Sum.inr (Sum.inr r) = (P.trans_tar_invFun Q c).val
--   ↔ r.val = (Q.iso_right.invFun c).val
--   := sorry

theorem PomEquiv.trans_src_invFun_eq_mid {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ) (b: β.carrier) (Hb) (a: α.carrier)
  : ⟨Sum.inl b, Hb⟩ = (P.trans_src_invFun Q a)
  ↔ (P.iso_right.invFun b).val = (P.iso_left.invFun a).val
  := by
    simp only [Set.Mem, Membership.mem, trans_sub_tar_pom] at Hb 
    simp only [trans_src_invFun]
    generalize Hqc: P.iso_left.invFun a = pa;
    cases pa
    simp only []
    split
    case inl H =>
      rw [Subtype.mk_eq_mk]
      rw [Sum.inl.inj_iff]
      rw [
        <-@EmbeddingLike.apply_eq_iff_eq _ _ _ _ 
          P.iso_right.symm.toEquiv b _,
      ]
      simp only [
        RelIso.coe_toEquiv, 
        Equiv.toFun_as_coe_apply, 
        Equiv.invFun_as_coe,
        PomIso.symm
      ]
      rw [RelIso.symm_apply_apply]
      exact Subtype.mk_eq_mk
    case inr H => 
      exact ⟨
        (λH => by cases H),
        λH' => by
          apply False.elim
          apply H
          rw [<-H']
          let ⟨_, H''⟩ := (P.iso_right.invFun b);
          exact H''
      ⟩  

theorem PomEquiv.trans_tar_invFun_eq_mid {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ) (b: β.carrier) (Hb) (c: γ.carrier)
  : ⟨Sum.inl b, Hb⟩ = (P.trans_tar_invFun Q c)
  ↔ (Q.iso_left.invFun b).val = (Q.iso_right.invFun c).val
  := by
    simp only [Set.Mem, Membership.mem, trans_sub_tar_pom] at Hb 
    simp only [trans_tar_invFun]
    generalize Hqc: Q.iso_right.invFun c = qc;
    cases qc
    simp only []
    split
    case inl H =>
      rw [Subtype.mk_eq_mk]
      rw [Sum.inl.inj_iff]
      rw [
        <-@EmbeddingLike.apply_eq_iff_eq _ _ _ _ 
          Q.iso_left.symm.toEquiv b _,
      ]
      simp only [
        RelIso.coe_toEquiv, 
        Equiv.toFun_as_coe_apply, 
        Equiv.invFun_as_coe,
        PomIso.symm
      ]
      rw [RelIso.symm_apply_apply]
      exact Subtype.mk_eq_mk
    case inr H => 
      exact ⟨
        (λH => by cases H),
        λH' => by
          apply False.elim
          apply H
          rw [<-H']
          let ⟨_, H''⟩ := (Q.iso_left.invFun b);
          exact H''
      ⟩  

theorem PomEquiv.trans_tar_invFun_eq_right' {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ) (r) (Hr) (c: γ.carrier)
  : ⟨Sum.inr (Sum.inr r), Hr⟩ = (P.trans_tar_invFun Q c)
  ↔ r.val = (Q.iso_right.invFun c).val
  := by
    simp only [Set.Mem, Membership.mem, trans_sub_tar_pom] at Hr 
    simp only [trans_tar_invFun]
    generalize Hqc: Q.iso_right.invFun c = qc;
    cases qc with
    | mk qc Hqc' =>
      simp only []
      split
      case inl H =>
        exact ⟨
          (λH => by cases H),
          λH' => by
            apply False.elim
            cases r with
            | mk r Hr =>
              have ⟨Hr, Hr'⟩ := Hr;
              apply Hr'
              rw [<-H'] at H
              exact H
        ⟩  
      case inr H => 
        cases r with
        | mk r Hr =>
          rw [Subtype.mk_eq_mk]
          rw [Sum.inr.inj_iff]
          rw [Sum.inr.inj_iff]
          rw [Subtype.mk_eq_mk]


theorem PomEquiv.trans_sub_invFun_eq_left' {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ) (r) (Hr) (a: α.carrier)
  : ⟨Sum.inr (Sum.inl r), Hr⟩ = (P.trans_src_invFun Q a)
  ↔ r.val = (P.iso_left.invFun a).val
  := by
    simp only [Set.Mem, Membership.mem, trans_sub_tar_pom] at Hr 
    simp only [trans_src_invFun]
    generalize Hqa: P.iso_left.invFun a = qa;
    cases qa
    simp only []
    split
    case inl H =>
      exact ⟨
        (λH => by cases H),
        λH' => by
          apply False.elim
          cases r with
          | mk r Hr =>
            sorry
            -- have ⟨Hr, Hr'⟩ := Hr;
            -- apply Hr'
            -- rw [<-H'] at H
            -- exact H
      ⟩  
    case inr H => 
      cases r with
      | mk r Hr =>
        rw [Subtype.mk_eq_mk]
        rw [Sum.inr.inj_iff]
        rw [Sum.inl.inj_iff]
        rw [Subtype.mk_eq_mk]

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

def PomEquiv.trans_sub_mid_iso {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  : PomIso (P.trans_sub_mid_pom Q) β
  := {
      toFun := λe => match e with | ⟨Sum.inl e, _⟩ => e,
      invFun := λe => ⟨Sum.inl e, True.intro⟩,
      left_inv := λe => match e with | ⟨Sum.inl e, _⟩ => rfl,
      right_inv := λ_ => rfl,
      map_rel_iff' := λ{a b} =>
        match a, b with
        | ⟨Sum.inl a, _⟩, ⟨Sum.inl b, _⟩ => by rfl,
      action_eq := λ{e} => match e with | ⟨Sum.inl e, _⟩ => rfl 
  }

theorem PomEquiv.trans_pom_mid_infinite_pred' {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ) (b: β.carrier)
  : Infinite ((P.trans_pom Q).pred (Sum.inl b)) ↔ Infinite (β.pred b)
  := ⟨
    λH => match trans_pom_pred_factor_infinite H with
    | Or.inl H => by
      rw [
        <-(trans_sub_mid_iso P Q).pred_infinite_iff',
        (SubPom.pred_iso _ _).infinite_iff
      ]
      exact H
    | Or.inr (Or.inl H) => 
      by
        have H: Infinite ((SubPom.univ P.shared).pred ⟨(P.iso_right.invFun b).val, True.intro⟩) 
          := @Infinite.of_injective _ _ H
            (λe => match e with 
            | ⟨Sum.inr (Sum.inl ⟨e, He⟩), He'⟩ => 
              ⟨
                e, 
                True.intro,
                He'.right
              ⟩
            )
            (λa b => match a, b with
              | ⟨Sum.inr (Sum.inl ⟨a, Ha'⟩), Ha⟩, ⟨Sum.inr (Sum.inl ⟨b, Hb'⟩), Hb⟩ 
                => λH => by cases H; rfl);
        have H := (P.reduce_right.is_reduct.pred_infinite_iff _).mp H;
        have H := (SubPom.pred_iso _ _).infinite_iff.mpr H;
        have H := (P.iso_right.pred_infinite_iff _).mp H;
        rw [P.iso_right.right_inv] at H
        exact H
    | Or.inr (Or.inr H) => 
      by
        have H: Infinite ((SubPom.univ Q.shared).pred ⟨(Q.iso_left.invFun b).val, True.intro⟩) 
          := @Infinite.of_injective _ _ H
            (λe => match e with 
            | ⟨Sum.inr (Sum.inr ⟨e, He⟩), He'⟩ => 
              ⟨
                e, 
                True.intro,
                He'.right
              ⟩
            )
            (λa b => match a, b with
              | ⟨Sum.inr (Sum.inr ⟨a, Ha'⟩), Ha⟩, ⟨Sum.inr (Sum.inr ⟨b, Hb'⟩), Hb⟩ 
                => λH => by cases H; rfl);
        have H := (Q.reduce_left.is_reduct.pred_infinite_iff _).mp H;
        have H := (SubPom.pred_iso _ _).infinite_iff.mpr H;
        have H := (Q.iso_left.pred_infinite_iff _).mp H;
        rw [Q.iso_left.right_inv] at H
        exact H,
    λH => @Infinite.of_injective _ _ H 
      (λ⟨b, Hb⟩ => ⟨Sum.inl b, Hb⟩) 
      (λ⟨a, Ha⟩ ⟨b, Hb⟩ H => by cases H; rfl)
  ⟩

theorem PomEquiv.trans_pom_mid_left_infinite_pred'' {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ) (b: β.carrier)
  : Infinite ((P.trans_pom Q).pred (Sum.inl b)) 
  ↔ Infinite (P.reduce_right.shared.pred (P.iso_right.invFun b))
  := by
    rw [
      trans_pom_mid_infinite_pred' P Q b,
      P.iso_right.symm.pred_infinite_iff _,
      (SubPom.pred_iso P.reduce_right.shared _).infinite_iff
    ]
    rfl

theorem PomEquiv.trans_pom_mid_right_infinite_pred'' {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ) (b: β.carrier)
  : Infinite ((P.trans_pom Q).pred (Sum.inl b)) 
  ↔ Infinite (Q.reduce_left.shared.pred (Q.iso_left.invFun b))
  := by
    rw [
      trans_pom_mid_infinite_pred' P Q b,
      Q.iso_left.symm.pred_infinite_iff _,
      (SubPom.pred_iso Q.reduce_left.shared _).infinite_iff
    ]
    rfl

theorem PomEquiv.trans_pom_mid_left_infinite_pred' {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ) (b: β.carrier)
  : Infinite ((P.trans_pom Q).pred (Sum.inl b)) 
  ↔ Infinite (P.shared.pred (P.iso_right.invFun b).val)
  := by
    rw [
      trans_pom_mid_left_infinite_pred'' P Q b,
      <-(SubPom.pred_iso _ _).infinite_iff,
      <-P.reduce_right.is_reduct.pred_infinite_iff',
      (SubPom.pred_iso _ _).infinite_iff,
      SubPom.univ_pred_pred_univ
    ]


theorem PomEquiv.trans_pom_mid_right_infinite_pred' {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ) (b: β.carrier)
  : Infinite ((P.trans_pom Q).pred (Sum.inl b)) 
  ↔ Infinite (Q.shared.pred (Q.iso_left.invFun b).val)
  := by
    rw [
      trans_pom_mid_right_infinite_pred'' P Q b,
      <-(SubPom.pred_iso _ _).infinite_iff,
      <-Q.reduce_left.is_reduct.pred_infinite_iff',
      (SubPom.pred_iso _ _).infinite_iff,
      SubPom.univ_pred_pred_univ
    ]

theorem PomEquiv.trans_pom_left_mid_left_infinite_helper {L} [Ticked L] {α β γ: Pom L}
  {P: PomEquiv α β} {Q: PomEquiv β γ} {e}
  (H: Infinite (SubPom.inter 
    (trans_sub_mid_pom P Q) 
    (Pom.pred (trans_pom P Q) (Sum.inr (Sum.inl e)))))
  : Infinite (α.pred (P.iso_left.toFun ⟨e.val, e.property.left⟩))
  := by
      rw [<-P.iso_left.pred_infinite_iff]
      rw [<-P.reduce_left.is_reduct.pred_infinite_iff']
      exact @Infinite.of_injective _ _ H
        (λ⟨Sum.inl b, _, Hb'⟩ => 
          ⟨⟨(P.iso_right.invFun b).val, True.intro⟩, Hb'⟩)
        (λ⟨Sum.inl a, Ha, Ha'⟩ ⟨Sum.inl b, Hb, Hb'⟩ H => 
          by 
            rw [Subtype.mk_eq_mk] at H
            simp only [Equiv.invFun_as_coe] at H 
            rw [Subtype.mk_eq_mk] at H
            have H := Subtype.eq H
            simp only [
              Equiv.toFun_as_coe_apply, 
              RelIso.coe_toEquiv, 
              EmbeddingLike.apply_eq_iff_eq
            ] at H
            cases H
            rfl
        )

theorem PomEquiv.trans_pom_right_mid_right_infinite_helper {L} [Ticked L] {α β γ: Pom L}
  {P: PomEquiv α β} {Q: PomEquiv β γ} {e}
  (H: Infinite (SubPom.inter 
    (trans_sub_mid_pom P Q) 
    (Pom.pred (trans_pom P Q) (Sum.inr (Sum.inr e)))))
  : Infinite (γ.pred (Q.iso_right.toFun ⟨e.val, e.property.left⟩))
  := by
      rw [<-Q.iso_right.pred_infinite_iff]
      rw [<-Q.reduce_right.is_reduct.pred_infinite_iff']
      exact @Infinite.of_injective _ _ H
        (λ⟨Sum.inl b, _, Hb'⟩ => 
          ⟨⟨(Q.iso_left.invFun b).val, True.intro⟩, Hb'⟩)
        (λ⟨Sum.inl a, Ha, Ha'⟩ ⟨Sum.inl b, Hb, Hb'⟩ H => 
          by 
            rw [Subtype.mk_eq_mk] at H
            simp only [Equiv.invFun_as_coe] at H 
            rw [Subtype.mk_eq_mk] at H
            have H := Subtype.eq H
            simp only [
              Equiv.toFun_as_coe_apply, 
              RelIso.coe_toEquiv, 
              EmbeddingLike.apply_eq_iff_eq
            ] at H
            cases H
            rfl
        )

theorem PomEquiv.trans_pom_right_left_mid_infinite_helper_finite {L} [Ticked L] {α β γ: Pom L}
  {P: PomEquiv α β} {Q: PomEquiv β γ} {e}
  (I: Infinite { c: Q.shared.carrier // ∃b: β.carrier,   
    Q.shared.order.le c (Q.iso_left.invFun b).val ∧
    P.shared.order.le (P.iso_right.invFun b).val e.val
  })
  (F: Finite { b: β.carrier // ∃c: Q.shared.carrier,  
    Q.shared.order.le c (Q.iso_left.invFun b).val ∧
    P.shared.order.le (P.iso_right.invFun b).val e.val
  })
  : Infinite (SubPom.inter 
    (trans_sub_mid_pom P Q) 
    (Pom.pred (trans_pom P Q) (Sum.inr (Sum.inl e))))
  := 
    let ⟨b, Hb⟩ := binary_predicate_pigeonhole _ I F;
    have ⟨_, _, Hb'⟩ := Hb.nonempty;
    have H := 
      (Q.reduce_left.is_reduct.pred_infinite_iff 
      (Q.iso_left.invFun b)).mp (
        @Infinite.of_injective _ _ Hb
          (λ⟨a, Ha⟩ => ⟨a, True.intro, Ha.left⟩)
          (λ⟨_, _⟩ ⟨_, _⟩ H => by cases H; rfl)
      )
    @Infinite.of_injective _ _ H
      (λ⟨q, Hq, Hq'⟩ => ⟨
        Sum.inl (Q.iso_left.toFun ⟨q, Hq⟩), True.intro, 
        P.shared.order.le_trans _ _ _ (
          P.iso_right.symm.map_rel_iff.mpr (by
            rw [<-Q.iso_left.right_inv b]
            apply Q.iso_left.map_rel_iff.mpr
            exact Hq'
          )
        ) 
        Hb'
      ⟩)
      (λ⟨a, Ha, Ha'⟩ ⟨b, Hb, Hb'⟩ => by 
        rw [Subtype.mk_eq_mk]
        rw [Sum.inl.inj_iff]
        intro H
        let H' := Q.iso_left.injective H;
        cases H';
        rfl
      )

theorem PomEquiv.trans_pom_left_right_mid_infinite_helper_finite {L} [Ticked L] {α β γ: Pom L}
  {P: PomEquiv α β} {Q: PomEquiv β γ} {e}
  (I: Infinite { a: P.shared.carrier // ∃b: β.carrier,   
    P.shared.order.le a (P.iso_right.invFun b).val ∧
    Q.shared.order.le (Q.iso_left.invFun b).val e.val
  })
  (F: Finite { b: β.carrier // ∃a: P.shared.carrier,  
    P.shared.order.le a (P.iso_right.invFun b).val ∧
    Q.shared.order.le (Q.iso_left.invFun b).val e.val
  })
  : Infinite (SubPom.inter 
    (trans_sub_mid_pom P Q) 
    (Pom.pred (trans_pom P Q) (Sum.inr (Sum.inr e))))
  := 
    let ⟨b, Hb⟩ := binary_predicate_pigeonhole _ I F;
    have ⟨_, _, Hb'⟩ := Hb.nonempty;
    have H := 
      (P.reduce_right.is_reduct.pred_infinite_iff 
      (P.iso_right.invFun b)).mp (
        @Infinite.of_injective _ _ Hb
          (λ⟨a, Ha⟩ => ⟨a, True.intro, Ha.left⟩)
          (λ⟨_, _⟩ ⟨_, _⟩ H => by cases H; rfl)
      )
    @Infinite.of_injective _ _ H
      (λ⟨q, Hq, Hq'⟩ => ⟨
        Sum.inl (P.iso_right.toFun ⟨q, Hq⟩), True.intro, 
        Q.shared.order.le_trans _ _ _ (
          Q.iso_left.symm.map_rel_iff.mpr (by
            rw [<-P.iso_right.right_inv b]
            apply P.iso_right.map_rel_iff.mpr
            exact Hq'
          )
        ) 
        Hb'
      ⟩)
      (λ⟨a, Ha, Ha'⟩ ⟨b, Hb, Hb'⟩ => by 
        rw [Subtype.mk_eq_mk]
        rw [Sum.inl.inj_iff]
        intro H
        let H' := P.iso_right.injective H;
        cases H';
        rfl
      )

theorem PomEquiv.trans_pom_right_left_mid_infinite_helper_infinite {L} [Ticked L] {α β γ: Pom L}
  {P: PomEquiv α β} {Q: PomEquiv β γ} {e}
  (H: Infinite { b: β.carrier // ∃c: Q.shared.carrier,  
    Q.shared.order.le c (Q.iso_left.invFun b).val ∧
    P.shared.order.le (P.iso_right.invFun b).val e.val
  })
  : Infinite (SubPom.inter 
    (trans_sub_mid_pom P Q) 
    (Pom.pred (trans_pom P Q) (Sum.inr (Sum.inl e))))
  := @Infinite.of_injective _ _ H
    (λ⟨b, Hb⟩ => ⟨Sum.inl b, True.intro, 
      let ⟨_, _, Hbe⟩ := Hb;
      Hbe
      ⟩)
    (λ⟨_, _⟩ ⟨_, _⟩ H => by cases H; rfl)

theorem PomEquiv.trans_pom_left_right_mid_infinite_helper_infinite {L} [Ticked L] {α β γ: Pom L}
  {P: PomEquiv α β} {Q: PomEquiv β γ} {e}
  (H: Infinite { b: β.carrier // ∃a: P.shared.carrier,  
    P.shared.order.le a (P.iso_right.invFun b).val ∧
    Q.shared.order.le (Q.iso_left.invFun b).val e.val
  })
  : Infinite (SubPom.inter 
    (trans_sub_mid_pom P Q) 
    (Pom.pred (trans_pom P Q) (Sum.inr (Sum.inr e))))
  := @Infinite.of_injective _ _ H
    (λ⟨b, Hb⟩ => ⟨Sum.inl b, True.intro, 
      let ⟨_, _, Hbe⟩ := Hb;
      Hbe
      ⟩)
    (λ⟨_, _⟩ ⟨_, _⟩ H => by cases H; rfl)

theorem PomEquiv.trans_pom_right_left_mid_infinite_helper_inner {L} [Ticked L] {α β γ: Pom L}
  {P: PomEquiv α β} {Q: PomEquiv β γ} {e}
  (H: Infinite { c: Q.shared.carrier // ∃b: β.carrier,  
    Q.shared.order.le c (Q.iso_left.invFun b).val ∧
    P.shared.order.le (P.iso_right.invFun b).val e.val
  })
  : Infinite (SubPom.inter 
    (trans_sub_mid_pom P Q) 
    (Pom.pred (trans_pom P Q) (Sum.inr (Sum.inl e))))
  := match finite_or_infinite _ with
  | Or.inl H' => trans_pom_right_left_mid_infinite_helper_finite H H'
  | Or.inr H => trans_pom_right_left_mid_infinite_helper_infinite H

theorem PomEquiv.trans_pom_left_right_mid_infinite_helper_inner {L} [Ticked L] {α β γ: Pom L}
  {P: PomEquiv α β} {Q: PomEquiv β γ} {e}
  (H: Infinite { a: P.shared.carrier // ∃b: β.carrier,  
    P.shared.order.le a (P.iso_right.invFun b).val ∧
    Q.shared.order.le (Q.iso_left.invFun b).val e.val
  })
  : Infinite (SubPom.inter 
    (trans_sub_mid_pom P Q) 
    (Pom.pred (trans_pom P Q) (Sum.inr (Sum.inr e))))
  := match finite_or_infinite _ with
  | Or.inl H' => trans_pom_left_right_mid_infinite_helper_finite H H'
  | Or.inr H => trans_pom_left_right_mid_infinite_helper_infinite H

theorem PomEquiv.trans_pom_right_left_mid_infinite_helper {L} [Ticked L] {α β γ: Pom L}
  {P: PomEquiv α β} {Q: PomEquiv β γ} {e}
  (H: Infinite (SubPom.inter 
    (trans_sub_right_rem_pom P Q) 
    (Pom.pred (trans_pom P Q) (Sum.inr (Sum.inl e)))))
  : Infinite (SubPom.inter 
    (trans_sub_mid_pom P Q) 
    (Pom.pred (trans_pom P Q) (Sum.inr (Sum.inl e))))
  := trans_pom_right_left_mid_infinite_helper_inner 
    (@Infinite.of_injective _ _ H 
      (λ⟨Sum.inr (Sum.inr ⟨c, _⟩), _, Hc'⟩ => ⟨c, Hc'⟩)
      (λ⟨Sum.inr (Sum.inr ⟨_, _⟩), _, _⟩ 
        ⟨Sum.inr (Sum.inr ⟨_, _⟩), _, _⟩ H 
        => by cases H; rfl)
    )

theorem PomEquiv.trans_pom_left_right_mid_infinite_helper {L} [Ticked L] {α β γ: Pom L}
  {P: PomEquiv α β} {Q: PomEquiv β γ} {e}
  (H: Infinite (SubPom.inter 
    (trans_sub_left_rem_pom P Q) 
    (Pom.pred (trans_pom P Q) (Sum.inr (Sum.inr e)))))
  : Infinite (SubPom.inter 
    (trans_sub_mid_pom P Q) 
    (Pom.pred (trans_pom P Q) (Sum.inr (Sum.inr e))))
  := trans_pom_left_right_mid_infinite_helper_inner 
    (@Infinite.of_injective _ _ H 
      (λ⟨Sum.inr (Sum.inl ⟨c, _⟩), _, Hc'⟩ => ⟨c, Hc'⟩)
      (λ⟨Sum.inr (Sum.inl ⟨_, _⟩), _, _⟩ 
        ⟨Sum.inr (Sum.inl ⟨_, _⟩), _, _⟩ H 
        => by cases H; rfl)
    )

theorem PomEquiv.trans_pom_left_infinite_pred' {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ) (e)
  : Infinite ((P.trans_pom Q).pred (Sum.inr (Sum.inl e))) 
  ↔ Infinite (α.pred (P.iso_left.toFun ⟨e.val, e.property.left⟩))
  := ⟨
    λH => match trans_pom_pred_factor_infinite H with
    | Or.inl H => trans_pom_left_mid_left_infinite_helper H
    | Or.inr (Or.inl H) => @Infinite.of_injective _ _ H
      (λ⟨Sum.inr (Sum.inl ⟨a, Ha, _⟩), _, Ha'⟩ => ⟨
        P.iso_left.toFun ⟨a, Ha⟩, 
        P.iso_left.map_rel_iff.mpr Ha'
      ⟩)
      (λ
        ⟨Sum.inr (Sum.inl ⟨a, Ha, _⟩), _, Ha'⟩ 
        ⟨Sum.inr (Sum.inl ⟨b, Hb, _⟩), _, Hb'⟩
        => by 
          intro H
          rw [Subtype.mk_eq_mk] at H
          simp only [
            Equiv.toFun_as_coe_apply, 
            RelIso.coe_toEquiv, 
            EmbeddingLike.apply_eq_iff_eq
          ] at H
          cases H
          rfl
        )
    | Or.inr (Or.inr H) => trans_pom_left_mid_left_infinite_helper
      (trans_pom_right_left_mid_infinite_helper H),
    λH => @Infinite.of_injective _ _ H 
      (λ⟨a, Ha⟩ => ⟨
        ((trans_sub_src_iso P Q).invFun a).val, 
        by
          have H := (trans_sub_src_iso P Q).left_inv ⟨(Sum.inr (Sum.inl e)), True.intro⟩;
          have H := congr_arg Subtype.val H;
          simp only [] at H
          rw [<-H]
          apply (trans_sub_src_iso P Q).symm.map_rel_iff.mpr
          exact Ha
        ⟩)
      (λ⟨a, Ha⟩ ⟨b, Hb⟩ H => by 
        rw [Subtype.mk_eq_mk] at H
        have H := Subtype.eq H
        simp at H
        cases H
        rfl
      )
  ⟩

def PomEquiv.trans_pom_left_infinite_pred'' {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ) (e)
  : Infinite ((P.trans_pom Q).pred (Sum.inr (Sum.inl e))) 
  ↔ Infinite 
    (α.pred ((trans_sub_src_iso P Q).toFun 
      ⟨Sum.inr (Sum.inl e), True.intro⟩))
  := trans_pom_left_infinite_pred' P Q e

theorem PomEquiv.trans_pom_right_infinite_pred' {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ) (e)
  : Infinite ((P.trans_pom Q).pred (Sum.inr (Sum.inr e))) 
  ↔ Infinite (γ.pred (Q.iso_right.toFun ⟨e.val, e.property.left⟩))
  := ⟨
    λH => match trans_pom_pred_factor_infinite H with
    | Or.inl H => trans_pom_right_mid_right_infinite_helper H
    | Or.inr (Or.inl H) => trans_pom_right_mid_right_infinite_helper
      (trans_pom_left_right_mid_infinite_helper H)
    | Or.inr (Or.inr H) => @Infinite.of_injective _ _ H
      (λ⟨Sum.inr (Sum.inr ⟨a, Ha, _⟩), _, Ha'⟩ => ⟨
        Q.iso_right.toFun ⟨a, Ha⟩, 
        Q.iso_right.map_rel_iff.mpr Ha'
      ⟩)
      (λ
        ⟨Sum.inr (Sum.inr ⟨a, Ha, _⟩), _, Ha'⟩ 
        ⟨Sum.inr (Sum.inr ⟨b, Hb, _⟩), _, Hb'⟩
        => by 
          intro H
          rw [Subtype.mk_eq_mk] at H
          simp only [
            Equiv.toFun_as_coe_apply, 
            RelIso.coe_toEquiv, 
            EmbeddingLike.apply_eq_iff_eq
          ] at H
          cases H
          rfl
        ),
    λH => @Infinite.of_injective _ _ H 
      (λ⟨a, Ha⟩ => ⟨
        ((trans_sub_tar_iso P Q).invFun a).val, 
        by
          have H := (trans_sub_tar_iso P Q).left_inv ⟨(Sum.inr (Sum.inr e)), True.intro⟩;
          have H := congr_arg Subtype.val H;
          simp only [] at H
          rw [<-H]
          apply (trans_sub_tar_iso P Q).symm.map_rel_iff.mpr
          exact Ha
        ⟩)
      (λ⟨a, Ha⟩ ⟨b, Hb⟩ H => by 
        rw [Subtype.mk_eq_mk] at H
        have H := Subtype.eq H
        simp at H
        cases H
        rfl
      )
  ⟩

def PomEquiv.trans_pom_right_infinite_pred'' {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ) (e)
  : Infinite ((P.trans_pom Q).pred (Sum.inr (Sum.inr e))) 
  ↔ Infinite 
    (γ.pred ((trans_sub_tar_iso P Q).toFun 
      ⟨Sum.inr (Sum.inr e), True.intro⟩))
  := trans_pom_right_infinite_pred' P Q e

def PomEquiv.trans_pom_mid_left_infinite_pred {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ) (b: β.carrier) (H)
  : Infinite ((P.trans_pom Q).pred (Sum.inl b)) 
  ↔ Infinite (α.pred ((P.trans_sub_src_iso Q).toFun ⟨Sum.inl b, H⟩))
  := by
    rw [
      trans_pom_mid_left_infinite_pred' P Q b,
      <-P.iso_left.pred_infinite_iff',
      <-P.reduce_left.is_reduct.pred_infinite_iff',
      (SubPom.pred_iso _ _).infinite_iff,
      SubPom.univ_pred_pred_univ
    ]
    simp only [trans_sub_src_iso, trans_src_toFun]
    rw [P.iso_left.left_inv]

def PomEquiv.trans_pom_mid_right_infinite_pred {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ) (b: β.carrier) (H)
  : Infinite ((P.trans_pom Q).pred (Sum.inl b)) 
  ↔ Infinite (γ.pred ((P.trans_sub_tar_iso Q).toFun ⟨Sum.inl b, H⟩))
  := by 
    rw [
      trans_pom_mid_right_infinite_pred' P Q b,
      <-Q.iso_right.pred_infinite_iff',
      <-Q.reduce_right.is_reduct.pred_infinite_iff',
      (SubPom.pred_iso _ _).infinite_iff,
      SubPom.univ_pred_pred_univ
    ]
    simp only [trans_sub_tar_iso, trans_tar_toFun]
    rw [Q.iso_right.left_inv]

def PomEquiv.trans_sub_src {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  : PomReduct (P.trans_pom Q)
  := {
    shared := P.trans_sub_src_pom Q,
    is_reduct := {
      subset := λ_ _ => True.intro,
      infinite_or_tick := λ⟨e, _⟩ => 
        match e with
        | Sum.inl e => 
          if p: (P.iso_right.invFun e).val ∈ P.reduce_left.shared.contains
          then Or.inl p
          else match P.right_rem_char _ p with
          | Or.inl p => Or.inr (Or.inl (
            have p := P.reduce_right.is_reduct.infinite_preserved _ p;
            have p := (SubPom.pred_iso _ _).infinite_iff.mpr p;
            have p := (P.iso_right.pred _).infinite_iff.mp p;
            @Infinite.of_injective _ _ p 
              (λ⟨e', He'⟩ => ⟨
                Sum.inl e', 
                ⟨True.intro, by {
                  simp at He';
                  exact He'
                }⟩
              ⟩) 
              (λ⟨a, Ha⟩ ⟨b, Hb⟩ H => by cases H; rfl)
          ))
          | Or.inr p => Or.inr (Or.inr ((P.right_action_eq _) ▸ p))
        | Sum.inr (Sum.inl e) => Or.inl True.intro
        | Sum.inr (Sum.inr ⟨e, p⟩) =>
          match Q.right_rem_char _ p.right with
          | Or.inl q => Or.inr (Or.inl (
            by {
              have q := Q.reduce_right.is_reduct.infinite_preserved ⟨e, p.left⟩ q;
              rw [<-(SubPom.pred_iso _ _).infinite_iff] at q;
              have q := (Q.iso_right.pred_infinite_iff _).mp q;
              exact @Infinite.of_injective _ _ q 
                (λ⟨e', He'⟩ => 
                let e'' :=  (P.trans_sub_tar_iso Q).symm.toFun  e';
                have H: e'' = P.trans_tar_invFun Q e' := rfl;
                  ⟨
                    e''.val, 
                    ⟨True.intro, 
                      match e'' with
                      | ⟨Sum.inl e'', _⟩ =>
                        have H := (P.trans_tar_invFun_eq_mid Q _ _ _).mp H;
                        have H := H ▸ (Q.right_shared_pred' _ _ p.left).mp He';
                        (P.trans_le_mid_right Q _ _).mpr H
                      | ⟨Sum.inr (Sum.inr ⟨e'', He'''⟩), _⟩ => 
                        have H := (P.trans_tar_invFun_eq_right' Q _ _ _).mp H;
                        have H := H.symm ▸ (Q.right_shared_pred' _ _ p.left).mp He';
                        (P.trans_le_right Q _ _).mpr H
                    ⟩
                  ⟩) 
                (λ⟨a, Ha⟩ ⟨b, Hb⟩ => by {
                  rw [Subtype.mk_eq_mk, Subtype.mk_eq_mk]
                  apply Function.Injective.comp
                  apply Subtype.val_injective
                  apply Equiv.injective
                })
            }
          ))
          | Or.inr p => Or.inr (Or.inr p)
      infinite_preserved := λe H =>
        match e with
        | ⟨Sum.inl e, He⟩ => 
          have H := (SubPom.univ_pred_pred_univ 
            (trans_pom P Q) 
            ⟨Sum.inl e, True.intro⟩) ▸ H;
          have H := (trans_pom_mid_left_infinite_pred P Q _ He).mp H;
          have H := ((trans_sub_src_iso P Q).pred_infinite_iff _).mpr H;
          (SubPom.pred_iso _ _).infinite_iff.mp H
        | ⟨Sum.inr (Sum.inl e), He⟩ => 
          have H := (SubPom.univ_pred_pred_univ 
            (trans_pom P Q) 
            ⟨Sum.inr (Sum.inl e), True.intro⟩) ▸ H;
          have H := (trans_pom_left_infinite_pred'' P Q _).mp H;
          have H := ((trans_sub_src_iso P Q).pred_infinite_iff _).mpr H;
          (SubPom.pred_iso _ _).infinite_iff.mp H,
      infinite_shared := 
        λH => 
          (P.trans_sub_src_iso Q).infinite_iff.mpr 
          ((P.trans_pom_left_infinite Q).mp (
            (SubPom.iso_univ _).infinite_iff.mp H
          )),
      empty_shared := λH => 
        (SubPom.iso_univ _).empty_iff.mpr (
          (P.trans_pom_left_empty Q).mpr (
            (P.trans_sub_src_iso Q).empty_iff.mp H
          )
        )
    }
  }

def PomEquiv.trans_sub_tar {L} [Ticked L] {α β γ: Pom L}
  (P: PomEquiv α β) (Q: PomEquiv β γ)
  : PomReduct (P.trans_pom Q)
  := {
    shared := P.trans_sub_tar_pom Q,
    is_reduct := {
      subset := λ_ _ => True.intro,
      infinite_or_tick := λ⟨e, _⟩ => 
        match e with
        | Sum.inl e => 
          if p: (Q.iso_left.invFun e).val ∈ Q.reduce_right.shared.contains
          then Or.inl p
          else match Q.left_rem_char _ p with
          | Or.inl p => Or.inr (Or.inl (
            have p := Q.reduce_left.is_reduct.infinite_preserved _ p;
            have p := (SubPom.pred_iso _ _).infinite_iff.mpr p;
            have p := (Q.iso_left.pred _).infinite_iff.mp p;
            @Infinite.of_injective _ _ p 
              (λ⟨e', He'⟩ => ⟨
                Sum.inl e', 
                ⟨True.intro, by {
                  simp at He';
                  exact He'
                }⟩
              ⟩) 
              (λ⟨a, Ha⟩ ⟨b, Hb⟩ H => by cases H; rfl)
          ))
          | Or.inr p => Or.inr (Or.inr ((Q.left_action_eq _) ▸ p))
        | Sum.inr (Sum.inl ⟨e, p⟩) =>           
          match P.left_rem_char _ p.right with
          | Or.inl q => Or.inr (Or.inl (
            by {
              have q := P.reduce_left.is_reduct.infinite_preserved ⟨e, p.left⟩ q;
              rw [<-(SubPom.pred_iso _ _).infinite_iff] at q;
              have q := (P.iso_left.pred_infinite_iff _).mp q;
              exact @Infinite.of_injective _ _ q 
                (λ⟨e', He'⟩ => 
                let e'' :=  (P.trans_sub_src_iso Q).symm.toFun  e';
                have H: e'' = P.trans_src_invFun Q e' := rfl;
                  ⟨
                    e''.val, 
                    ⟨True.intro, 
                      match e'' with
                      | ⟨Sum.inl e'', _⟩ =>
                        have H := (P.trans_src_invFun_eq_mid Q _ _ _).mp H;
                        have H := H ▸ (P.left_shared_pred' _ _ p.left).mp He';
                        (P.trans_le_mid_left Q _ _).mpr H
                      | ⟨Sum.inr (Sum.inl ⟨e'', He'''⟩), _⟩ =>
                        have H := (P.trans_sub_invFun_eq_left' Q _ _ _).mp H;
                        have H := H.symm ▸ (P.left_shared_pred' _ _ p.left).mp He';
                        (P.trans_le_left Q _ _).mpr H
                    ⟩
                  ⟩) 
                (λ⟨a, Ha⟩ ⟨b, Hb⟩ => by {
                  rw [Subtype.mk_eq_mk, Subtype.mk_eq_mk]
                  apply Function.Injective.comp
                  apply Subtype.val_injective
                  apply Equiv.injective
                })
            }
          ))
          | Or.inr p => Or.inr (Or.inr p)
        | Sum.inr (Sum.inr e) => Or.inl True.intro,
      infinite_preserved := λe H =>
        match e with
        | ⟨Sum.inl e, He⟩ => 
          have H := (SubPom.univ_pred_pred_univ 
            (trans_pom P Q) 
            ⟨Sum.inl e, True.intro⟩) ▸ H;
          have H := (trans_pom_mid_right_infinite_pred P Q _ He).mp H;
          have H := ((trans_sub_tar_iso P Q).pred_infinite_iff _).mpr H;
          (SubPom.pred_iso _ _).infinite_iff.mp H
        | ⟨Sum.inr (Sum.inr e), He⟩ => 
          have H := (SubPom.univ_pred_pred_univ 
            (trans_pom P Q) 
            ⟨Sum.inr (Sum.inr e), True.intro⟩) ▸ H;
          have H := (trans_pom_right_infinite_pred'' P Q _).mp H;
          have H := ((trans_sub_tar_iso P Q).pred_infinite_iff _).mpr H;
          (SubPom.pred_iso _ _).infinite_iff.mp H,
      infinite_shared := λH => 
          (P.trans_sub_tar_iso Q).infinite_iff.mpr 
          ((P.trans_pom_right_infinite Q).mp (
            (SubPom.iso_univ _).infinite_iff.mp H
          )),
      empty_shared := λH => 
        (SubPom.iso_univ _).empty_iff.mpr (
          (P.trans_pom_right_empty Q).mpr (
            (P.trans_sub_tar_iso Q).empty_iff.mp H
          )
        )
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