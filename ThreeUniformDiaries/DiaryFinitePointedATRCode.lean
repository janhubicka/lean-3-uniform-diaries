import ThreeUniformDiaries.DiaryFinitePointedEnvelope
import ThreeUniformDiaries.FiniteAuxEmbeddingImage

/-!
# A diary pointed envelope is a genuine FINITE ATR embedding

The native pointed-envelope structure contains exact singleton and
auxiliary meet equalities on its first `size` vertices. These imply
the finite cut-by-cut type-reflection clauses used by the verified
finite auxiliary Ramsey theorem. In particular the finite envelope
is represented by precisely its `Fin size` actual vertex images;
its arbitrary increasing continuation cannot affect the colouring.

This closes the bridge from a finite pointed envelope to the
actual `FiniteAuxEmbeddingImage` API, not a synthetic infinite
aux-type-respecting embedding of the whole continuation.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Auxiliary-type agreement at a cut is equivalent to the capped
auxiliary meet being at/after that cut, provided both ordered pairs
begin no earlier than the cut. -/
theorem auxMeetLevel_ge_iff_sameAuxTypeBelow
    (K : Ordered3Graph Nat)
    (w a b c d : Nat) (hwa : w ≤ a) (hwc : w ≤ c) :
    w ≤ K.auxMeetLevel a b c d ↔
      K.SameAuxTypeBelow w a b c d := by
  classical
  constructor
  · intro hw z hz
    exact (K.auxMeetLevel_agree a b c d)
      (lt_of_lt_of_le hz hw)
  · intro htype
    exact Nat.le_findGreatest (le_min hwa hwc) htype

private theorem strictMono_le_iff
    (f : Nat → Nat) (hf : StrictMono f) (a b : Nat) :
    f a ≤ f b ↔ a ≤ b := by
  constructor
  · intro h
    by_contra hn
    have hba : b < a := Nat.lt_of_not_ge hn
    exact (not_lt_of_ge h) (hf hba)
  · intro h
    exact hf.monotone h

namespace FinitePointedEnvelope

variable {K : Ordered3Graph Nat} {j a b : Nat}

/-- On actual finite source vertices, exact singleton meets are
equivalent to preservation/reflection of singleton type agreements
at EVERY selected cut, including target levels outside the image. -/
theorem one_cut_iff
    (E : FinitePointedEnvelope K j a b)
    (w u v : Nat) (hwu : w ≤ u) (hwv : w ≤ v)
    (hu : u < E.size) (hv : v < E.size) :
    E.induced.SameOneTypeBelow w u v ↔
      K.SameOneTypeBelow (E.enumerate w)
        (E.enumerate u) (E.enumerate v) := by
  have hsource :=
    E.induced.oneMeetLevel_ge_iff_sameOneTypeBelow
      w u v hwu hwv
  have htarget :=
    K.oneMeetLevel_ge_iff_sameOneTypeBelow
      (E.enumerate w) (E.enumerate u) (E.enumerate v)
      (E.strictMono.monotone hwu)
      (E.strictMono.monotone hwv)
  constructor
  · intro hs
    apply htarget.mp
    rw [E.singleton_meets u v hu hv]
    exact E.strictMono.monotone (hsource.mpr hs)
  · intro ht
    apply hsource.mp
    have hle := htarget.mpr ht
    rw [E.singleton_meets u v hu hv] at hle
    exact (strictMono_le_iff E.enumerate E.strictMono w
      (E.induced.oneMeetLevel u v)).mp hle

/-- The same reflection statement for the actual auxiliary 2-types
of two ordered pairs inside the finite pointed envelope. -/
theorem aux_cut_iff
    (E : FinitePointedEnvelope K j a b)
    (w u v x y : Nat) (hwu : w ≤ u) (huv : u < v)
    (hwx : w ≤ x) (hxy : x < y)
    (hv : v < E.size) (hy : y < E.size) :
    E.induced.SameAuxTypeBelow w u v x y ↔
      K.SameAuxTypeBelow (E.enumerate w)
        (E.enumerate u) (E.enumerate v)
        (E.enumerate x) (E.enumerate y) := by
  have hsource :=
    E.induced.auxMeetLevel_ge_iff_sameAuxTypeBelow
      w u v x y hwu hwx
  have htarget :=
    K.auxMeetLevel_ge_iff_sameAuxTypeBelow
      (E.enumerate w) (E.enumerate u) (E.enumerate v)
      (E.enumerate x) (E.enumerate y)
      (E.strictMono.monotone hwu)
      (E.strictMono.monotone hwx)
  constructor
  · intro hs
    apply htarget.mp
    rw [E.auxiliary_meets u v x y huv hxy hv hy]
    exact E.strictMono.monotone (hsource.mpr hs)
  · intro ht
    apply hsource.mp
    have hle := htarget.mpr ht
    rw [E.auxiliary_meets u v x y huv hxy hv hy] at hle
    exact (strictMono_le_iff E.enumerate E.strictMono w
      (E.induced.auxMeetLevel u v x y)).mp hle

/-- The native envelope's canonical inclusion is an actual finite
aux-type-respecting embedding of its induced enumerated hypergraph.
There are NO obligations on an artificial infinite source tail. -/
theorem finite_aux_embedding
    (E : FinitePointedEnvelope K j a b) :
    FiniteAuxEmbedding E.induced K E.enumerate E.size := by
  refine {
    strictMono := E.strictMono
    edge_iff := ?_
    one := ?_
    aux := ?_
  }
  · intro u v w huv hvw hw
    exact Iff.rfl
  · intro w u v hwu hwv hu hv
    exact E.one_cut_iff w u v hwu hwv hu hv
  · intro w u v x y hwu huv hwx hxy hv hy
    exact E.aux_cut_iff w u v x y hwu huv hwx hxy hv hy

/-- Canonical extensional finite-image code that may be used as
a genuine input to a finite ATR colouring. -/
def finiteCode (E : FinitePointedEnvelope K j a b) :
    FiniteAuxEmbeddingImage E.induced K E.size :=
  FiniteAuxEmbeddingImage.ofFiniteAuxEmbedding
    E.enumerate E.finite_aux_embedding

/-- The finite code fixes the whole protected prefix literally. -/
theorem finiteCode_fix_prefix
    (E : FinitePointedEnvelope K j a b)
    (t : Fin E.size) (ht : t.val < j) :
    E.finiteCode.image t = t.val := by
  change E.enumerate t.val = t.val
  exact E.protected_prefix t.val ht

/-- The endpoint markers refer to the final two ACTUAL finite
vertices of the code, independently of any chosen extension. -/
theorem finiteCode_final_endpoints
    (E : FinitePointedEnvelope K j a b) :
    E.finiteCode.image
        ⟨E.size - 2, by have hh := E.size_lower; omega⟩ = a ∧
      E.finiteCode.image
        ⟨E.size - 1, by have hh := E.size_lower; omega⟩ = b := by
  constructor
  · change E.enumerate (E.size - 2) = a
    exact E.first_endpoint
  · change E.enumerate (E.size - 1) = b
    exact E.second_endpoint

end FinitePointedEnvelope
end Ordered3Graph
end ThreeUniformDiaries
