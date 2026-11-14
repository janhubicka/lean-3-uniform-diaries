import ThreeUniformDiaries.DiaryEventualRangeIndexEscape
import ThreeUniformDiaries.DiaryCofinalBoundedCountableFusion
import ThreeUniformDiaries.DiaryNonEscapeEquivalentToPersistence

/-!
# Track D: exact RELATIVE persistent successor criterion in original F indices

The remaining countable diary fusion gate is relative to a SPECIFIC
already fixed old complete reserved stage f on S_m. The checked
criterion persistentSuccessor_iff_cofinalBoundedNextLeafImages says
that a persistent successor fixing f exists iff cofinally late
compatible genuine finite-horizon stages can keep the NEW leaf
m below one numerical target bound.

This module translates that exact RELATIVE criterion into a uniform
bound on a CHOSEN original F-preimage index of m in such compatible
stages. No monotonicity, injectivity or surjectivity of F is needed.
The finite section lemma handles bounded target values, and the
finite F-image of a bounded index prefix handles the converse.

Its sharp negation is the already recognized eventual escape from
every finite original F-source index prefix, equivalently the failure
of every fixed-image cofinal relative successor.

These are interfaces and obstructions. They do not prove the
bounded-index hypothesis in actual arbitrary prescribed generic
subcopies or the unconditional countable diary unavoidability theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- For a fixed old stage f and genuine source next leaf m,
a finitely persistent *COMPATIBLE* genuine successor exists
IFF a SINGLE original F-index cutoff T is sufficient for some
actual compatible reserved horizon witness at arbitrarily late
future source horizons.

The maps g, indices t and horizons n can vary with N. The
source/target leaf range F may be unordered and noninjective.
The old support f is fixed BEFORE T and all future horizons. -/
theorem persistentRelativeSuccessor_iff_cofinalBoundedNewLeafIndex
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (hm : IsLeaf H m) :
    (∃ g : Nat → Nat,
      PersistentReservedDiaryStage H K F (m + 1) g ∧
      CofinalDiaryStageCompatible H m f g) ↔
    (∃ T : Nat, ∀ N : Nat,
      ∃ n : Nat, N ≤ n ∧
        ∃ g : Nat → Nat,
          ReservedDiaryStage H K F (m + 1 + n) g ∧
          CofinalDiaryStageCompatible H m f g ∧
          ∃ t : Nat, t < T ∧ g m = F t) := by
  classical
  constructor
  · intro hSucc
    obtain ⟨B, hBound⟩ :=
      (persistentSuccessor_iff_cofinalBoundedNextLeafImages
        (H := H) (K := K) (F := F) (f := f) (m := m)
        hm).mp hSucc
    obtain ⟨T, hSection⟩ :=
      bounded_range_values_have_bounded_preimage_indices F B
    refine ⟨T, ?_⟩
    intro N
    obtain ⟨n, hn, g, Q, hOld, hSmall⟩ := hBound N
    have hmSupported :
        m ∈ countableDiaryFiniteSupport H (m + 1 + n) :=
      mem_finiteLeafMeetSupport_leaf H
        (countableDiaryLeafPrefix H (m + 1 + n)) m
        ((mem_countableDiaryLeafPrefix_iff H (m + 1 + n) m).mpr
          ⟨hm.1, by omega, hm⟩)
    obtain ⟨t, ht⟩ := Q.1.leaf_range m hmSupported hm
    obtain ⟨t', ht', htImage⟩ :=
      hSection (g m) hSmall ⟨t, ht.symm⟩
    exact ⟨n, hn, g, Q, hOld, t', ht', htImage.symm⟩
  · rintro ⟨T, hIndex⟩
    apply (persistentSuccessor_iff_cofinalBoundedNextLeafImages
      (H := H) (K := K) (F := F) (f := f) (m := m)
      hm).mpr
    refine ⟨(Finset.range T).sup F, ?_⟩
    intro N
    obtain ⟨n, hn, g, Q, hOld, t, ht, hImage⟩ := hIndex N
    refine ⟨n, hn, g, Q, hOld, ?_⟩
    rw [hImage]
    exact Finset.le_sup (f := F) (Finset.mem_range.mpr ht)

/-- For the SAME specified old f, failure of a persistent
compatible next leaf is EQUIVALENT to every genuine old-compatible
later finite reserved stage eventually avoiding each bounded
prefix F[0,T) in the original unordered generic enumeration.

The escape may be vacuous without existence of horizon witnesses.
For finitely persistent old f, the checked existing theorem separately
supplies genuine witnesses at each later horizon. -/
theorem noPersistentRelativeSuccessor_iff_eventualNewLeafIndexEscape
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (hm : IsLeaf H m) :
    (¬ ∃ g : Nat → Nat,
      PersistentReservedDiaryStage H K F (m + 1) g ∧
      CofinalDiaryStageCompatible H m f g) ↔
    EventuallyEscapingNextLeafRangeIndices H K F f m := by
  classical
  constructor
  · intro hNo
    have hNum : EventuallyNumericallyEscapingNextLeaf H K F f m := by
      by_contra hNot
      exact hNo
        ((persistentSuccessor_iff_not_uniform_escape
          (H := H) (K := K) (F := F) (f := f) (m := m) hm).mpr hNot)
    exact (eventualNumericEscape_iff_eventualRangeIndexEscape
      (H := H) (K := K) (F := F) (f := f) (m := m) hm).mp hNum
  · intro hIndex hSucc
    have hNum : EventuallyNumericallyEscapingNextLeaf H K F f m :=
      (eventualNumericEscape_iff_eventualRangeIndexEscape
        (H := H) (K := K) (F := F) (f := f) (m := m) hm).mpr hIndex
    exact ((persistentSuccessor_iff_not_uniform_escape
      (H := H) (K := K) (F := F) (f := f) (m := m) hm).mp
      hSucc) hNum

end DiaryLeafPriority
end ThreeUniformDiaries
