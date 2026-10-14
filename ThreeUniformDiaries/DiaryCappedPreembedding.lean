import ThreeUniformDiaries.DiaryChosenPreembedding
import ThreeUniformDiaries.DiaryCappedPairReduction

/-!
# Completing the capped leaf-pair meet case

The full meet of two diary leaf pairs can be capped at their
first leaf. The source reduction proves their first leaves are
equal and (unless the second leaves coincide) the singleton
meet of the second leaves is a genuine 1-split AFTER that first
leaf.

The witness-chosen pre-embedding maps such a later 1-split to
the ACTUAL target singleton meet of the second leaves. Its
predecessor interval therefore puts this meet after the target
image of the common first leaf.

That single target singleton inequality forces equality of
both second-coordinate singleton profiles and all auxiliary
bits for the two pairs through the common first target leaf.
Hence the full target 2-type meet is capped exactly there.

No all-level global pair-type preservation through omitted
target indices is assumed. This closes the capped case for
the proposed target images of LEAF PAIRS, not the marker-1
orientation or the full flip/pre-embedding theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RoleDiary

open Ordered3Graph
open Ordered3Graph.UnorderedEmbedding

variable {H : Ordered3Graph Nat}

/-- If the full source type meet of (a,b) and (c,d) is capped,
the target singleton meet of b and d lies strictly beyond the
target image of a. For distinct b,d this follows from the
source late one-split and the genuine target witness image;
for b=d it follows from the diagonal singleton meet. -/
theorem capped_second_leaves_target_meet_later
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (D : RoleDiary H)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hcap : H.twoMeetLevel a b c d = min a c) :
    let φ := stabilisedSource G K F ψ
    φ a < K.oneMeetLevel (φ b) (φ d) := by
  let φ := stabilisedSource G K F ψ
  by_cases hbd : b = d
  · subst d
    have hself : K.oneMeetLevel (φ b) (φ b) = φ b := by
      have hupper : K.oneMeetLevel (φ b) (φ b) ≤ φ b := by
        simpa only [min_self] using
          K.oneMeetLevel_le_min (φ b) (φ b)
      have hSame : K.SameOneTypeBelow (φ b) (φ b) (φ b) := by
        intro x y hxy hy
        rfl
      have hlower : φ b ≤ K.oneMeetLevel (φ b) (φ b) :=
        (K.oneMeetLevel_ge_iff_sameOneTypeBelow
          (φ b) (φ b) (φ b)
          (by omega) (by omega)).mpr hSame
      exact Nat.le_antisymm hupper hlower
    rw [hself]
    exact φ.strictMono hab
  · have hSourceLater : a < H.oneMeetLevel b d :=
      D.capped_leaf_pairs_second_meet_later
        a b c d hab hcd ha hb hc hd hbd hcap
    let m := H.oneMeetLevel b d
    have hm : IsOneSplit H m := D.singleton_meets b d hb hd hbd
    have hle : m ≤ min b d := H.oneMeetLevel_le_min b d
    have hneB : m ≠ b := by
      intro heq
      have hs : IsOneSplit H b := by simpa only [heq] using hm
      exact hb.2.1 hs.2.1
    have hneD : m ≠ d := by
      intro heq
      have hs : IsOneSplit H d := by simpa only [heq] using hm
      exact hd.2.1 hs.2.1
    have hmb : m < b := by omega
    have hmd : m < d := by omega
    have hImage :
        D.oneSplitTargetImage G K F ψ m hm =
          K.oneMeetLevel (φ b) (φ d) :=
      D.oneSplitTargetImage_eq_any_witness
        G K F ψ hψ m b d hm hb hd hmb hmd rfl
    have hInt := D.oneSplitTargetImage_interval
      G K F ψ hψ m hm
    have hPre : a ≤ m-1 := by
      dsimp [m]
      omega
    have hMon : φ a ≤ φ (m-1) :=
      φ.strictMono.monotone hPre
    calc
      φ a ≤ φ (m-1) := hMon
      _ < D.oneSplitTargetImage G K F ψ m hm := hInt.1
      _ = K.oneMeetLevel (φ b) (φ d) := hImage

/-- The capped case of the leaf-pair meet preservation condition
for the proposed diary pre-embedding is now unconditional under
the complete V/E/S diary axioms and the verified fused I2 map.

The target meet of the images of the two leaf pairs agrees
literally with the chosen pre-embedding image of their source
capped full meet. -/
theorem chosenPreembedding_preserves_capped_pair_meet
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (D : RoleDiary H)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hcap : H.twoMeetLevel a b c d = min a c) :
    let φ := stabilisedSource G K F ψ
    K.twoMeetLevel (φ a) (φ b) (φ c) (φ d) =
      D.chosenPreembedding G K F ψ (min a c) := by
  let φ := stabilisedSource G K F ψ
  have hLater : φ a < K.oneMeetLevel (φ b) (φ d) :=
    D.capped_second_leaves_target_meet_later
      G K F ψ hψ a b c d hab hcd ha hb hc hd hcap
  have hExact :
      K.twoMeetLevel (φ a) (φ b) (φ c) (φ d) = φ a :=
    D.capped_leaf_pair_target_of_late_singleton φ
      a b c d hab hcd ha hc hcap hLater
  have hac : a = c :=
    D.capped_leaf_pairs_first_eq a b c d hab hcd ha hc hcap
  have hmin : min a c = a := by
    rw [← hac]
    simp
  rw [hmin, D.chosenPreembedding_leaf G K F ψ a ha]
  exact hExact

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
