import Sparky.PomEquiv.Basic

def PomEquiv.sigma
  {L} [Ticked L]
  {N} [PartialOrder N]
  (F: N -> Pom L)
  (G: N -> Pom L)
  (E: ∀(n: N), PomEquiv (F n) (G n))
  : PomEquiv (Pom.sigma F) (Pom.sigma G)
  := {
    shared := Pom.sigma (λn => (E n).shared),
    reduce_left := {
      shared := sorry,
      is_reduct := sorry
    },
    reduce_right := sorry,
    iso_left := sorry,
    iso_right := sorry
  }