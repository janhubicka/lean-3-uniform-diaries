import ThreeUniformDiaries.DiaryFinitePointedATRCode

/-!
# A reusable finite ATR embedding constructor from exact meets

The genuine finite Aemb API requires preservation AND reflection of
singleton and auxiliary type equality at every eligible selected
cut. An equivalent and often easier hypothesis is literal exact
preservation of the corresponding capped meets on all ACTUAL
source vertices, together with an induced-edge embedding there.

This is especially useful for the selected three-tail source
embedded into a four-tail amalgam with one inserted vertex:
the original source may omit target enumeration levels, but the
exact early meet computations can still be checked directly.

The theorem is finite and independent of the diary V/E/S axioms,
genericity, Milliken, or the Ramsey theorem. It makes no claims
about the infinitely zero-extended continuation of a finite source.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph
namespace FiniteAuxEmbedding

/-- Any strictly increasing finite induced map preserving ALL
actual singleton and auxiliary meets is a genuine finite ATR
embedding. Equality of type cuts then follows by comparing
their (capped) meet levels and using strict order reflection.

This avoids proving every type-cut equivalence separately once
the finite meet table has been audited. -/
theorem of_exact_meets
    {H K : Ordered3Graph Nat} (f : Nat → Nat) (m : Nat)
    (hf : StrictMono f)
    (hEdge :
      ∀ a b c, a < b → b < c → c < m →
        (H.edge a b c ↔ K.edge (f a) (f b) (f c)))
    (hOne :
      ∀ u v, u < m → v < m →
        K.oneMeetLevel (f u) (f v) =
          f (H.oneMeetLevel u v))
    (hAux :
      ∀ a b c d, a < b → c < d → b < m → d < m →
        K.auxMeetLevel (f a) (f b) (f c) (f d) =
          f (H.auxMeetLevel a b c d)) :
    FiniteAuxEmbedding H K f m := by
  refine {
    strictMono := hf
    edge_iff := hEdge
    one := ?_
    aux := ?_
  }
  · intro w u v hwu hwv hu hv
    have hs :=
      H.oneMeetLevel_ge_iff_sameOneTypeBelow
        w u v hwu hwv
    have ht :=
      K.oneMeetLevel_ge_iff_sameOneTypeBelow
        (f w) (f u) (f v)
        (hf.monotone hwu) (hf.monotone hwv)
    constructor
    · intro hsource
      apply ht.mp
      rw [hOne u v hu hv]
      exact hf.monotone (hs.mpr hsource)
    · intro htarget
      apply hs.mp
      have hle : f w ≤ f (H.oneMeetLevel u v) := by
        simpa only [hOne u v hu hv] using (ht.mpr htarget)
      by_contra hn
      have hw : H.oneMeetLevel u v < w := Nat.lt_of_not_ge hn
      exact (not_lt_of_ge hle) (hf hw)
  · intro w a b c d hwa hab hwc hcd hb hd
    have hs :=
      H.auxMeetLevel_ge_iff_sameAuxTypeBelow
        w a b c d hwa hwc
    have ht :=
      K.auxMeetLevel_ge_iff_sameAuxTypeBelow
        (f w) (f a) (f b) (f c) (f d)
        (hf.monotone hwa) (hf.monotone hwc)
    constructor
    · intro hsource
      apply ht.mp
      rw [hAux a b c d hab hcd hb hd]
      exact hf.monotone (hs.mpr hsource)
    · intro htarget
      apply hs.mp
      have hle : f w ≤ f (H.auxMeetLevel a b c d) := by
        simpa only [hAux a b c d hab hcd hb hd] using
          (ht.mpr htarget)
      by_contra hn
      have hw : H.auxMeetLevel a b c d < w :=
        Nat.lt_of_not_ge hn
      exact (not_lt_of_ge hle) (hf hw)

end FiniteAuxEmbedding
end Ordered3Graph
end ThreeUniformDiaries
