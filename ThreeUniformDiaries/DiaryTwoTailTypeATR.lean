import ThreeUniformDiaries.DiaryRoleThreeTailATR
import ThreeUniformDiaries.DiaryTwoTailATR

/-!
# The two-tail ATR criterion transported from a source type-respecting pair

The two-tail case has no exterior auxiliary-pair comparison.
Consequently source leaf pairs with singleton meet before the
cut need only exact singleton-meet transport to become ATR-admissible
selected carriers in a gappy target.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Every prefix-plus-two-tail selected carrier of a type-respecting
embedding is ATR-admissible when its two leaf types separate before
the source cut. No diary-specific marker axioms are needed. -/
theorem two_tail_ATR_after_type_embedding
    {H K : Ordered3Graph Nat}
    (ψ : Embedding H K) (hψ : ψ.TypeRespecting)
    (i a b : Nat) (hearly : H.oneMeetLevel a b < i)
    (f : Nat → Nat) (hf : StrictMono f)
    (hfix : ∀ t, t < ψ i → f t = t)
    (hfA : f (ψ i) = ψ a)
    (hfB : f (ψ i + 1) = ψ b) :
    (∀ u v, u < ψ i + 2 → v < ψ i + 2 →
      K.oneMeetLevel (f u) (f v) =
        f ((K.pullback f).oneMeetLevel u v)) ∧
    (∀ c d e g, c < d → e < g →
      d < ψ i + 2 → g < ψ i + 2 →
      K.auxMeetLevel (f c) (f d) (f e) (f g) =
        f ((K.pullback f).auxMeetLevel c d e g)) := by
  have htail : K.oneMeetLevel (f (ψ i)) (f (ψ i + 1)) < ψ i := by
    calc
      K.oneMeetLevel (f (ψ i)) (f (ψ i + 1)) =
        K.oneMeetLevel (ψ a) (ψ b) := by rw [hfA, hfB]
      _ = ψ (H.oneMeetLevel a b) :=
        typeRespecting_oneMeetLevel_eq ψ hψ a b
      _ < ψ i := ψ.strictMono hearly
  exact K.pointed_two_tail_ATR_finite f hf (ψ i) hfix htail

end Ordered3Graph
end ThreeUniformDiaries
