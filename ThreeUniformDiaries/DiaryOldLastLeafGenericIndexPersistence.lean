import ThreeUniformDiaries.DiaryNonrelativeNewLeafBoundPersistence
import ThreeUniformDiaries.DiaryEventualRangeIndexEscape

/-!
# Track D: cofinal last-old-leaf index bounds and exact escape

The verified old-support finite-vector compactness theorem says that
some complete genuinely reserved old S_m support is finitely persistent
IFF the target numeric image of the LAST selected old source leaf b
is bounded along cofinally late genuine finite source horizons.

This module translates that criterion to ORIGINAL F-PREIMAGE INDICES,
with NO target order/monotonicity condition on the prescribed leaf map F.
A bounded numerical range has a uniformly bounded chosen F-index
section; conversely the finite image of an initial index segment is
numerically bounded. Every genuine reserved stage maps each selected
old leaf into the original F[Nat] range.

The exact dual assertion is that if no old support is persistent,
the same fixed last old leaf b eventually avoids ALL bounded original
generic-index prefixes at every future source horizon. In full
diaries the escape is nonvacuous, by the independently verified
genuine reserved finite-stage existence theorem.

For a true new source leaf m, the last leaf at horizon m+1 IS m.
This gives the corresponding NONRELATIVE next-leaf index criterion.

These are quantified equivalences and obstructions, not existence of
a persistent extension of any *preselected* old map. The missing
relative successor property and countable diary unavoidability remain
unproved.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Given a nonempty genuinely selected old leaf set L_m, a
persistent COMPLETE old S1/S2 support exists iff the last old
source leaf b has a chosen F-preimage index below ONE bound T
in genuine reserved stages at arbitrarily late source horizons.

F need not be ordered, injective, or surjective. -/
theorem persistentOldSupport_iff_cofinalBoundedLastOldLeafIndex
    (H K : Ordered3Graph Nat) (F : Nat → Nat) (m : Nat)
    (hOld : (countableDiaryLeafPrefix H m).Nonempty) :
    (∃ f : Nat → Nat,
      PersistentReservedDiaryStage H K F m f) ↔
    (∃ T : Nat, ∀ N : Nat,
      ∃ n : Nat, N ≤ n ∧
        ∃ g : Nat → Nat,
          ReservedDiaryStage H K F (m + n) g ∧
          ∃ t : Nat, t < T ∧
            g ((countableDiaryLeafPrefix H m).max' hOld) = F t) := by
  classical
  let L := countableDiaryLeafPrefix H m
  let b := L.max' hOld
  have hb : b ∈ L := Finset.max'_mem L hOld
  have hbLeaf : IsLeaf H b :=
    ((mem_countableDiaryLeafPrefix_iff H m b).mp hb).2.2
  have hbSupported : b ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H L b hb
  constructor
  · intro hPersistent
    obtain ⟨B, hBound⟩ :=
      (persistentOldSupport_iff_cofinalBoundedLastOldLeaf
        H K F m hOld).mp hPersistent
    obtain ⟨T, hSection⟩ :=
      bounded_range_values_have_bounded_preimage_indices F B
    refine ⟨T, ?_⟩
    intro N
    obtain ⟨n, hn, g, Q, hSmall⟩ := hBound N
    have hbStage : b ∈ countableDiaryFiniteSupport H (m + n) :=
      (countableDiaryFiniteSupport_mono H m (m + n) (by omega))
        hbSupported
    obtain ⟨t, hAt⟩ := Q.1.leaf_range b hbStage hbLeaf
    have hNumeric : g b ≤ B := by
      simpa only [b, L] using hSmall
    obtain ⟨t', ht', htAt⟩ :=
      hSection (g b) hNumeric ⟨t, hAt.symm⟩
    refine ⟨n, hn, g, Q, t', ht', ?_⟩
    change g b = F t'
    exact htAt.symm
  · rintro ⟨T, hAll⟩
    apply (persistentOldSupport_iff_cofinalBoundedLastOldLeaf
      H K F m hOld).mpr
    refine ⟨(Finset.range T).sup F, ?_⟩
    intro N
    obtain ⟨n, hn, g, Q, t, ht, hImage⟩ := hAll N
    refine ⟨n, hn, g, Q, ?_⟩
    change g b ≤ (Finset.range T).sup F
    change g b = F t at hImage
    rw [hImage]
    exact Finset.le_sup (f := F) (Finset.mem_range.mpr ht)

/-- Exact dual to the previous iff: if no complete persistent old
support exists, the SAME fixed last old source leaf eventually
has no F-preimage index inside ANY prescribed finite index prefix
in any genuine reserved future stage.

The quantifier is `∀T ∃N ∀n≥N ∀g ∀t<T, g(b)≠F(t)`;
no monotonicity of F or target-enumeration assumption occurs. -/
theorem noPersistentOldSupport_iff_eventualLastOldLeafIndexEscape
    (H K : Ordered3Graph Nat) (F : Nat → Nat) (m : Nat)
    (hOld : (countableDiaryLeafPrefix H m).Nonempty) :
    (¬ ∃ f : Nat → Nat,
      PersistentReservedDiaryStage H K F m f) ↔
    (∀ T : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
      ∀ g : Nat → Nat,
        ReservedDiaryStage H K F (m + n) g →
        ∀ t : Nat, t < T →
          g ((countableDiaryLeafPrefix H m).max' hOld) ≠ F t) := by
  classical
  let L := countableDiaryLeafPrefix H m
  let b := L.max' hOld
  have hb : b ∈ L := Finset.max'_mem L hOld
  have hbLeaf : IsLeaf H b :=
    ((mem_countableDiaryLeafPrefix_iff H m b).mp hb).2.2
  have hbSupported : b ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H L b hb
  constructor
  · intro hNo T
    have hNumeric :=
      (noPersistentOldSupport_iff_eventualLastOldLeafEscape
        H K F m hOld).mp hNo
    let B := (Finset.range T).sup F
    obtain ⟨N, hAll⟩ := hNumeric B
    refine ⟨N, ?_⟩
    intro n hn g Q t ht hEq
    have hSmall : F t ≤ B :=
      Finset.le_sup (f := F) (Finset.mem_range.mpr ht)
    have hLarge : B < g b := by
      simpa only [b, L] using hAll n hn g Q
    change g b = F t at hEq
    rw [hEq] at hLarge
    omega
  · intro hIndex
    apply (noPersistentOldSupport_iff_eventualLastOldLeafEscape
      H K F m hOld).mpr
    intro B
    obtain ⟨T, hSection⟩ :=
      bounded_range_values_have_bounded_preimage_indices F B
    obtain ⟨N, hAll⟩ := hIndex T
    refine ⟨N, ?_⟩
    intro n hn g Q
    by_contra hNot
    have hSmall : g b ≤ B := by
      change ¬ B < g b at hNot
      omega
    have hbStage : b ∈ countableDiaryFiniteSupport H (m + n) :=
      (countableDiaryFiniteSupport_mono H m (m + n) (by omega))
        hbSupported
    obtain ⟨t, hAt⟩ := Q.1.leaf_range b hbStage hbLeaf
    obtain ⟨t', ht', htAt⟩ :=
      hSection (g b) hSmall ⟨t, hAt.symm⟩
    have hForbidden := hAll n hn g Q t' ht'
    have hImage : g b = F t' := htAt.symm
    exact hForbidden hImage

/-- When the next genuine source leaf m is freely chosen without a
preassigned old map, existence of SOME persistent S_(m+1) stage
is equivalent to a uniformly bounded ORIGINAL F-preimage index
for the new leaf in cofinally late genuine future stages. -/
theorem persistentNextStage_iff_cofinalBoundedNewLeafIndex
    (H K : Ordered3Graph Nat) (F : Nat → Nat)
    (m : Nat) (hm : IsLeaf H m) :
    (∃ g : Nat → Nat,
      PersistentReservedDiaryStage H K F (m + 1) g) ↔
    (∃ T : Nat, ∀ N : Nat,
      ∃ n : Nat, N ≤ n ∧
        ∃ g : Nat → Nat,
          ReservedDiaryStage H K F (m + 1 + n) g ∧
          ∃ t : Nat, t < T ∧ g m = F t) := by
  obtain ⟨hOld, hLast⟩ :=
    max_selected_leaf_at_true_successor H m hm
  simpa only [hLast] using
    (persistentOldSupport_iff_cofinalBoundedLastOldLeafIndex
      H K F (m + 1) hOld)

/-- Exact nonrelative new-leaf index-escape alternative. The
possible old map remains existential and is not required to
extend a prescribed persistent stage from source horizon m. -/
theorem noPersistentNextStage_iff_eventualNewLeafIndexEscape
    (H K : Ordered3Graph Nat) (F : Nat → Nat)
    (m : Nat) (hm : IsLeaf H m) :
    (¬ ∃ g : Nat → Nat,
      PersistentReservedDiaryStage H K F (m + 1) g) ↔
    (∀ T : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
      ∀ g : Nat → Nat,
        ReservedDiaryStage H K F (m + 1 + n) g →
        ∀ t : Nat, t < T → g m ≠ F t) := by
  obtain ⟨hOld, hLast⟩ :=
    max_selected_leaf_at_true_successor H m hm
  simpa only [hLast] using
    (noPersistentOldSupport_iff_eventualLastOldLeafIndexEscape
      H K F (m + 1) hOld)

end DiaryLeafPriority
end ThreeUniformDiaries
