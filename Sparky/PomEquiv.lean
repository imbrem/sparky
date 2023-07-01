import Sparky.PomEquiv.Basic
import Sparky.PomEquiv.Trans
import Sparky.PomEquiv.Sigma

def PomEquivP {L} [Ticked L] (α β: Pom L): Prop := Nonempty (PomEquiv α β)

def PomEquivP.refl {L} [Ticked L] (α: Pom L): PomEquivP α α 
  := Nonempty.intro (PomEquiv.refl α)

def PomEquivP.symm {L} [Ticked L] {α β: Pom L} (P: PomEquivP α β): PomEquivP β α
  := let ⟨P⟩ := P; Nonempty.intro P.symm

def PomEquivP.trans {L} [Ticked L] {α β γ: Pom L} (P: PomEquivP α β) (Q: PomEquivP β γ): PomEquivP α γ 
  := let ⟨P⟩ := P; let ⟨Q⟩ := Q; Nonempty.intro (PomEquiv.trans P Q)

def PomEquivP.iseqv {L} [HL: Ticked L]: Equivalence (@PomEquivP L HL) := {
  refl := refl,
  symm := symm,
  trans := trans
}

instance Pom.isSetoid (L) [Ticked L] : Setoid (Pom L) := {
  r := PomEquivP,
  iseqv := PomEquivP.iseqv
}

def PomFamilyEquivP {N} {L} [Ticked L] (F G: PomFamily N L): Prop 
  := Nonempty (PomFamilyEquiv F G)

def PomFamilyEquivP.refl {N} {L} [Ticked L] (F: PomFamily N L): PomFamilyEquivP F F 
  := Nonempty.intro (PomFamilyEquiv.refl F)

def PomFamilyEquivP.symm {N} {L} [Ticked L] 
  {F G: PomFamily N L} (E: PomFamilyEquivP F G): PomFamilyEquivP G F
  := let ⟨E⟩ := E; Nonempty.intro E.symm

def PomFamilyEquivP.trans {N} {L} [Ticked L] 
  {F G H: PomFamily N L} (E: PomFamilyEquivP F G) (E': PomFamilyEquivP G H)
  : PomFamilyEquivP F H 
  := let ⟨E⟩ := E; let ⟨E'⟩ := E'; Nonempty.intro (PomFamilyEquiv.trans E E')

def PomFamilyEquivP.iseqv {N} {L} [HL: Ticked L]
  : Equivalence (@PomFamilyEquivP N L HL) := {
  refl := refl,
  symm := symm,
  trans := trans
}

instance PomFamily.isSetoid (N) (L) [Ticked L] : Setoid (PomFamily N L) := {
  r := PomFamilyEquivP,
  iseqv := PomFamilyEquivP.iseqv
}

def Pom' (L) [Ticked L] := Quotient (Pom.isSetoid L)
def Pom.toPom' {L} [Ticked L]: Pom L -> Pom' L := Quotient.mk _

def Pom'.empty (L) [Ticked L]: Pom' L := (Pom.empty L).toPom'
def Pom'.tick (L) [Ticked L]: Pom' L := (Pom.tick L).toPom'

def Pom'.seq {L} [Ticked L]: Pom' L -> Pom' L -> Pom' L 
  := Quotient.lift₂ 
    (λα β => (α.seq β).toPom') 
    (λ_ _ _ _ Hα Hβ => 
      let ⟨Hα⟩ := Hα;
      let ⟨Hβ⟩ := Hβ;
      Quotient.sound (Nonempty.intro (Hα.seq Hβ))     
    )
def Pom'.seq_mk {L} [Ticked L] (α β: Pom L):
  (α.seq β).toPom' = α.toPom'.seq β.toPom' 
  := sorry

def Pom'.par {L} [Ticked L]: Pom' L -> Pom' L -> Pom' L 
  := Quotient.lift₂ 
    (λα β => (α.par β).toPom') 
    (λ_ _ _ _ Hα Hβ => 
      let ⟨Hα⟩ := Hα;
      let ⟨Hβ⟩ := Hβ;
      Quotient.sound (Nonempty.intro (Hα.par Hβ))     
    )

def Pom'.empty_seq {L} [Ticked L] (α: Pom' L): α.seq (Pom'.empty L) = α 
  := sorry
def Pom'.seq_empty {L} [Ticked L] (α: Pom' L): (Pom'.empty L).seq α = α 
  := sorry
def Pom'.seq_assoc {L} [Ticked L] (α β γ: Pom' L): (α.seq β).seq γ = α.seq (β.seq γ) 
  := sorry

instance {L} [Ticked L]: Monoid (Pom' L) := {
  mul := Pom'.seq,
  mul_assoc := Pom'.seq_assoc,
  one := Pom'.empty L,
  one_mul := Pom'.seq_empty,
  mul_one := Pom'.empty_seq
}

def Pom'.empty_par {L} [Ticked L] (α: Pom' L): α.par (Pom'.empty L) = α
  := sorry
def Pom'.par_empty {L} [Ticked L] (α: Pom' L): (Pom'.empty L).par α = α
  := sorry
def Pom'.par_assoc {L} [Ticked L] (α β γ: Pom' L): (α.par β).par γ = α.par (β.par γ) 
  := sorry
def Pom'.par_comm {L} [Ticked L] (α β: Pom' L): α.par β = β.par α
  := sorry

instance {L} [Ticked L]: AddMonoid (Pom' L) := {
  add := Pom'.par,
  add_assoc := Pom'.par_assoc,
  zero := Pom'.empty L,
  zero_add := Pom'.par_empty,
  add_zero := Pom'.empty_par
}

def PomFamily' (N) (L) [Ticked L] := Quotient (PomFamily.isSetoid N L)
def PomFamily'.mk {N} {L} [Ticked L]: PomFamily N L -> PomFamily' N L 
  := Quotient.mk _
def PomFamily'.app {N} {L} [Ticked L]: PomFamily' N L -> N -> Pom' L
  := Quotient.lift (λF n => (F n).toPom') (λ_ _ E => 
    let ⟨E⟩ := E; funext (λn => Quotient.sound (Nonempty.intro (E n))))

abbrev PomFamily.toPomFamily' {N} {L} [Ticked L]
  : PomFamily N L -> PomFamily' N L 
  := Quotient.mk _
def PomFamily'.mk_app {N} {L} [Ticked L] (F: PomFamily N L) (n: N)
  : F.toPomFamily'.app n = (F n).toPom'
  := sorry
abbrev PomFamily.toPom' {N} [PartialOrder N] {L} [Ticked L] (F: PomFamily N L): Pom' L
  := F.toPom.toPom'
abbrev PomFamily'.toPom' {N} [PartialOrder N] {L} [Ticked L]: PomFamily' N L -> Pom' L
  := Quotient.lift PomFamily.toPom' 
    (λ_ _ H => let ⟨H⟩ := H; Quotient.sound (Nonempty.intro H.toPomEquiv))
theorem PomFamily'.mk_toPom' {N} [PartialOrder N] {L} [Ticked L] (F: PomFamily N L)
  : F.toPomFamily'.toPom' = F.toPom'
  := sorry

def PomFamily'.map_index {L} [Ticked L] {N M} 
  : PomFamily' N L -> (M -> N) -> PomFamily' M L
  := Quotient.lift 
    (λF f => Quotient.mk _ (F.map_index f)) 
    (λ_ _ E => let ⟨E⟩ := E; funext (λf => Quotient.sound (Nonempty.intro (λm => E (f m)))))
def PomFamily'.mk_map_index {L} [Ticked L] {N M} (F: PomFamily N L) (f: M -> N)
  : F.toPomFamily'.map_index f = (F.map_index f).toPomFamily'
  := sorry
abbrev PomFamily'.succ {L} [Ticked L] (F: PomFamily' ℕ L): PomFamily' ℕ L
  := F.map_index Nat.succ
def PomFamily'.succ_sigma {L} [Ticked L] (F: PomFamily' ℕ L)
  : F.toPom' = (F.app 0).seq F.succ.toPom'
  := Quotient.inductionOn F 
    (λF => by
      rw [mk_app, mk_toPom', succ, mk_map_index, mk_toPom', <-Pom'.seq_mk]
      exact Quotient.sound (Nonempty.intro (PomEquiv.fromRightIso (PomIso.succ_sigma F)))
    )