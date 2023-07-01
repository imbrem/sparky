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

def Pom' (L) [Ticked L] := Quotient (Pom.isSetoid L)

def Pom.toEquiv {L} [Ticked L]: Pom L -> Pom' L := Quotient.mk _
def Pom'.empty (L) [Ticked L]: Pom' L := (Pom.empty L).toEquiv
def Pom'.tick (L) [Ticked L]: Pom' L := (Pom.tick L).toEquiv

def Pom'.seq {L} [Ticked L]: Pom' L -> Pom' L -> Pom' L 
  := Quotient.lift₂ 
    (λα β => (α.seq β).toEquiv) 
    (λ_ _ _ _ Hα Hβ => 
      let ⟨Hα⟩ := Hα;
      let ⟨Hβ⟩ := Hβ;
      Quotient.sound (Nonempty.intro (Hα.seq Hβ))     
    )
--def Pom'.empty_left_unit_seq {L} [Ticked L] (α: Pom' L)