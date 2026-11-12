import ThreeUniformDiaries.DiaryFiniteE2E3E5Gate
import ThreeUniformDiaries.DiaryFiniteCandidateCriterion

/-!
# Track A: a genuine finite generator candidate needs only E2/E3/E5 incidence checks

For a full source and target diary, functionality of the proposed
S1/S2 generator table determines each selected leaf image and its
exact singleton meet image. With order and role preservation, the
verified general finite E2/E3/E5 gate then reduces the candidate's
induced edge/nonedge requirement to just three finite families.

This does not establish existence or functionality of any candidate,
nor future reserve or countable-source unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- All exact S1 meet transport needed by the finite E2/E3/E5
edge gate is already forced by a *functional* candidate generator
table, since every genuine supported leaf belongs to the selected
leaf set and the table contains the numeric S1 generator row. -/
theorem functional_candidate_induced_of_E2_E3_E5
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (F f : Nat → Nat) (m v : Nat)
    (hFunctional : FiniteGeneratorTableFunctional
      (candidateNewLeafGeneratorTable H K m f v))
    (hOrdered : ∀ a b : Nat,
      a ∈ countableDiaryFiniteSupport H (m + 1) →
      b ∈ countableDiaryFiniteSupport H (m + 1) →
      a < b →
      candidateNewLeafTableMap H K m f v a <
        candidateNewLeafTableMap H K m f v b)
    (hLeafRole : ∀ a : Nat,
      a ∈ countableDiaryFiniteSupport H (m + 1) →
      IsLeaf H a → IsLeaf K (candidateNewLeafTableMap H K m f v a))
    (hOneRole : ∀ a : Nat,
      a ∈ countableDiaryFiniteSupport H (m + 1) →
      IsOneSplit H a → IsOneSplit K (candidateNewLeafTableMap H K m f v a))
    (hTwoRole : ∀ a : Nat,
      a ∈ countableDiaryFiniteSupport H (m + 1) →
      IsTwoSplit H a → IsTwoSplit K (candidateNewLeafTableMap H K m f v a))
    (hE2 : ∀ s b : Nat,
      s ∈ countableDiaryFiniteSupport H (m + 1) →
      b ∈ countableDiaryFiniteSupport H (m + 1) →
      IsOneSplit H s → IsLeaf H b → s < b →
      (H.edge 0 s b ↔ K.edge 0
        (candidateNewLeafTableMap H K m f v s)
        (candidateNewLeafTableMap H K m f v b)))
    (hE3 : ∀ s a b : Nat,
      s ∈ countableDiaryFiniteSupport H (m + 1) →
      a ∈ countableDiaryFiniteSupport H (m + 1) →
      b ∈ countableDiaryFiniteSupport H (m + 1) →
      IsTwoSplit H s → IsLeaf H a → IsLeaf H b →
      s < a → a < b →
      (H.edge s a b ↔ K.edge
        (candidateNewLeafTableMap H K m f v s)
        (candidateNewLeafTableMap H K m f v a)
        (candidateNewLeafTableMap H K m f v b)))
    (hE5 : ∀ a b c : Nat,
      a ∈ countableDiaryFiniteSupport H (m + 1) →
      b ∈ countableDiaryFiniteSupport H (m + 1) →
      c ∈ countableDiaryFiniteSupport H (m + 1) →
      IsLeaf H a → IsLeaf H b → IsLeaf H c →
      a < b → b < c →
      (H.edge a b c ↔ K.edge
        (candidateNewLeafTableMap H K m f v a)
        (candidateNewLeafTableMap H K m f v b)
        (candidateNewLeafTableMap H K m f v c))) :
    ∀ a b c : Nat,
      a ∈ countableDiaryFiniteSupport H (m + 1) →
      b ∈ countableDiaryFiniteSupport H (m + 1) →
      c ∈ countableDiaryFiniteSupport H (m + 1) →
      a < b → b < c →
      (H.edge a b c ↔ K.edge
        (candidateNewLeafTableMap H K m f v a)
        (candidateNewLeafTableMap H K m f v b)
        (candidateNewLeafTableMap H K m f v c)) := by
  classical
  let L := countableDiaryLeafPrefix H (m + 1)
  let S := countableDiaryFiniteSupport H (m + 1)
  let q := candidateNewLeafTableMap H K m f v
  have hLLeaf (a : Nat) (ha : a ∈ L) : IsLeaf H a :=
    ((mem_countableDiaryLeafPrefix_iff H (m + 1) a).mp ha).2.2
  have hOnlyLeaves (a : Nat) (ha : a ∈ S)
      (hLeaf : IsLeaf H a) : a ∈ L :=
    finiteLeafMeetSupport_leaf_mem_L DH hLLeaf ha hLeaf
  have hMarkerS (i : Nat) (hi : i < 3) : i ∈ S :=
    mem_finiteLeafMeetSupport_marker H L i hi
  have hMarker (i : Nat) (hi : i < 3) : q i = i := by
    change finiteGeneratorTableValue
      (candidateNewLeafGeneratorTable H K m f v) i = i
    exact finiteGeneratorTableValue_eq_of_mem _
      hFunctional i i
      (finiteLeafGeneratorTable_marker H K L
        (candidateLeafImage f m v) i hi)
  have hSelected (a : Nat) (ha : a ∈ L) :
      q a = candidateLeafImage f m v a := by
    change finiteGeneratorTableValue
      (candidateNewLeafGeneratorTable H K m f v) a =
      candidateLeafImage f m v a
    exact finiteGeneratorTableValue_eq_of_mem _
      hFunctional a _
      (finiteLeafGeneratorTable_leaf H K L
        (candidateLeafImage f m v) a ha)
  have hMeet (a b : Nat)
      (ha : a ∈ S) (hb : b ∈ S) (hab : a < b)
      (hLa : IsLeaf H a) (hLb : IsLeaf H b) :
      H.oneMeetLevel a b ∈ S ∧
      K.oneMeetLevel (q a) (q b) = q (H.oneMeetLevel a b) := by
    have haL : a ∈ L := hOnlyLeaves a ha hLa
    have hbL : b ∈ L := hOnlyLeaves b hb hLb
    have hRow :
        (H.oneMeetLevel a b,
          K.oneMeetLevel (candidateLeafImage f m v a)
            (candidateLeafImage f m v b)) ∈
          candidateNewLeafGeneratorTable H K m f v :=
      finiteLeafGeneratorTable_oneMeet H K L
        (candidateLeafImage f m v) a b haL hbL (ne_of_lt hab)
    have hValue : q (H.oneMeetLevel a b) =
        K.oneMeetLevel (candidateLeafImage f m v a)
          (candidateLeafImage f m v b) := by
      change finiteGeneratorTableValue
        (candidateNewLeafGeneratorTable H K m f v)
        (H.oneMeetLevel a b) =
          K.oneMeetLevel (candidateLeafImage f m v a)
            (candidateLeafImage f m v b)
      exact finiteGeneratorTableValue_eq_of_mem _
        hFunctional _ _ hRow
    refine ⟨mem_finiteLeafMeetSupport_oneMeet H L a b
      haL hbL (ne_of_lt hab), ?_⟩
    calc
      K.oneMeetLevel (q a) (q b) =
          K.oneMeetLevel (candidateLeafImage f m v a)
            (candidateLeafImage f m v b) := by
          rw [hSelected a haL, hSelected b hbL]
      _ = q (H.oneMeetLevel a b) := hValue.symm
  exact (DH.finite_induced_iff_E2_E3_E5 DK S q
      (hMarkerS 0 (by omega))
      (hMarkerS 1 (by omega))
      (hMarkerS 2 (by omega))
      (hMarker 0 (by omega))
      (hMarker 1 (by omega))
      (hMarker 2 (by omega))
      hOrdered hLeafRole hOneRole hTwoRole hMeet).mpr
        ⟨hE2, hE3, hE5⟩

end DiaryLeafPriority
end ThreeUniformDiaries
