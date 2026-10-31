import ThreeUniformDiaries.ActualFiniteEmbeddingMeets

/-!
# Track A: exact numeric meets suffice for actual finite ATR codes

The upper-bound factorisation must produce a *genuine*
FiniteAuxEmbeddingImage, not a type-respecting picture with an
uncontrolled infinite zero-extension. Here we prove the reusable
converse of the already validated finite exact-meet implication:

For a strictly increasing, induced finite map f on [0,m), preservation
of ALL capped singleton meets and capped auxiliary pair meets is
SUFFICIENT for the full finite auxiliary-type-respecting interface.

The point is the exact equivalence
    SameTypeBelow w ... <-> w <= meetLevel ...
at cuts not exceeding the relevant cap. Strict monotonicity of f
then transports the inequality both ways, even across skipped
target positions. No unverified diary axiom, envelope, or infinite
branch theorem is used here.

The diary-specific outstanding obligation is to establish the
two numeric-meet identities for the actual finite induced leaf-meet
support in a RoleDiary. The necessary finite-role machinery exists
in the repository, but that transport is NOT asserted by this file.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Cut agreement is exactly comparison with the capped
first-disagreement level, provided the cut lies below both
vertices. This includes the cap case. -/
theorem sameOneTypeBelow_iff_le_numeric_meet
    (H : Ordered3Graph Nat) (w u v : Nat)
    (hwu : w ≤ u) (hwv : w ≤ v) :
    H.SameOneTypeBelow w u v ↔
      w ≤ H.oneMeetLevel u v := by
  constructor
  · intro h
    exact Nat.le_findGreatest (le_min hwu hwv) h
  · intro h a b hab hb
    exact (H.oneMeetLevel_agree u v) hab (lt_of_lt_of_le hb h)

/-- The analogous capped-meet characterisation for auxiliary
types of ordered pairs. -/
theorem sameAuxTypeBelow_iff_le_numeric_meet
    (H : Ordered3Graph Nat)
    (w u₀ u₁ v₀ v₁ : Nat)
    (hwu : w ≤ u₀) (hwv : w ≤ v₀) :
    H.SameAuxTypeBelow w u₀ u₁ v₀ v₁ ↔
      w ≤ H.auxMeetLevel u₀ u₁ v₀ v₁ := by
  constructor
  · intro h
    exact Nat.le_findGreatest (le_min hwu hwv) h
  · intro h a ha
    exact (H.auxMeetLevel_agree u₀ u₁ v₀ v₁)
      (lt_of_lt_of_le ha h)

/-- A strictly increasing map reflects numerical comparison as
well as preserving it. Avoid dependence on a stronger API for
the same elementary fact. -/
private theorem le_iff_image_le_of_strictMono
    (f : Nat → Nat) (hf : StrictMono f)
    (x y : Nat) :
    x ≤ y ↔ f x ≤ f y := by
  constructor
  · exact hf.monotone
  · intro h
    by_contra hn
    have hyx : y < x := by omega
    have hwrong : f y < f x := hf hyx
    omega

/-- FINITE auxiliary-type-respecting embedding obtained purely
from exact numeric singleton and auxiliary meets, together with
increasing induced edges. Every quantified vertex is an ACTUAL
source vertex below m.

This is the converse of FiniteAuxEmbedding.oneMeetLevel_eq
and FiniteAuxEmbedding.auxMeetLevel_eq for finite tuples. -/
theorem FiniteAuxEmbedding.of_exact_numeric_meets
    (H K : Ordered3Graph Nat) (f : Nat → Nat) (m : Nat)
    (hf : StrictMono f)
    (hEdge : ∀ a b c : Nat, a < b → b < c → c < m →
      (H.edge a b c ↔ K.edge (f a) (f b) (f c)))
    (hOne : ∀ u v : Nat, u < m → v < m →
      K.oneMeetLevel (f u) (f v) =
        f (H.oneMeetLevel u v))
    (hAux : ∀ a b c d : Nat,
      a < b → c < d → b < m → d < m →
      K.auxMeetLevel (f a) (f b) (f c) (f d) =
        f (H.auxMeetLevel a b c d)) :
    FiniteAuxEmbedding H K f m := by
  refine ⟨hf, hEdge, ?_, ?_⟩
  · intro w u v hwu hwv hu hv
    have hfu : f w ≤ f u := hf.monotone hwu
    have hfv : f w ≤ f v := hf.monotone hwv
    rw [H.sameOneTypeBelow_iff_le_numeric_meet
        w u v hwu hwv,
      K.sameOneTypeBelow_iff_le_numeric_meet
        (f w) (f u) (f v) hfu hfv,
      hOne u v hu hv]
    exact le_iff_image_le_of_strictMono f hf w
      (H.oneMeetLevel u v)
  · intro w a b c d hwa hab hwc hcd hb hd
    have hfa : f w ≤ f a := hf.monotone hwa
    have hfc : f w ≤ f c := hf.monotone hwc
    rw [H.sameAuxTypeBelow_iff_le_numeric_meet
        w a b c d hwa hwc,
      K.sameAuxTypeBelow_iff_le_numeric_meet
        (f w) (f a) (f b) (f c) (f d) hfa hfc,
      hAux a b c d hab hcd hb hd]
    exact le_iff_image_le_of_strictMono f hf w
      (H.auxMeetLevel a b c d)

end Ordered3Graph
end ThreeUniformDiaries
