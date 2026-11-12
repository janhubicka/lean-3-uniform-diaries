import ThreeUniformDiaries.DiaryCandidateE2E3E5Gate
import ThreeUniformDiaries.DiaryFiniteCandidateCriterion

/-!
# Track A: exact reduced finite candidate criterion

The full original finite candidate condition has a single large
induced-edge field. For full RoleDiary H and K, this field is
EQUIVALENT to the three finite edge/nonedge families E2, E3 and E5,
once the other explicit candidate fields (generator-table
functionality, strict order and roles) are retained.

E1 role markers and E4 Devlin pair markers follow automatically.
S1 and S2 exact numeric meet values remain encoded by generator-table
functionality. This is not existence of a target candidate, a
reserved extension, or countable diary unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The same fixed-v finite candidate checks as the existing
FiniteNewLeafCandidateCondition, except its opaque full induced
edge/nonedge table is replaced by the three genuinely independent
permitted-edge families E2, E3 and E5 on the WHOLE finite support.

In particular E2 and E3 also range over newly generated split
vertices lying before selected OLD leaves. -/
structure FiniteNewLeafE2E3E5CandidateCondition
    (H K : Ordered3Graph Nat) (F : Nat → Nat)
    (m : Nat) (f : Nat → Nat) (v : Nat) : Prop where
  functional : FiniteGeneratorTableFunctional
    (candidateNewLeafGeneratorTable H K m f v)
  leaf : IsLeaf K v
  range : ∃ t : Nat, v = F t
  ordered : ∀ a b : Nat,
    a ∈ countableDiaryFiniteSupport H (m + 1) →
    b ∈ countableDiaryFiniteSupport H (m + 1) →
    a < b →
    candidateNewLeafTableMap H K m f v a <
      candidateNewLeafTableMap H K m f v b
  leaf_role : ∀ a : Nat,
    a ∈ countableDiaryFiniteSupport H (m + 1) →
    IsLeaf H a → IsLeaf K (candidateNewLeafTableMap H K m f v a)
  one_split_role : ∀ a : Nat,
    a ∈ countableDiaryFiniteSupport H (m + 1) →
    IsOneSplit H a → IsOneSplit K (candidateNewLeafTableMap H K m f v a)
  two_split_role : ∀ a : Nat,
    a ∈ countableDiaryFiniteSupport H (m + 1) →
    IsTwoSplit H a → IsTwoSplit K (candidateNewLeafTableMap H K m f v a)
  e2 : ∀ s b : Nat,
    s ∈ countableDiaryFiniteSupport H (m + 1) →
    b ∈ countableDiaryFiniteSupport H (m + 1) →
    IsOneSplit H s → IsLeaf H b → s < b →
    (H.edge 0 s b ↔ K.edge 0
      (candidateNewLeafTableMap H K m f v s)
      (candidateNewLeafTableMap H K m f v b))
  e3 : ∀ s a b : Nat,
    s ∈ countableDiaryFiniteSupport H (m + 1) →
    a ∈ countableDiaryFiniteSupport H (m + 1) →
    b ∈ countableDiaryFiniteSupport H (m + 1) →
    IsTwoSplit H s → IsLeaf H a → IsLeaf H b →
    s < a → a < b →
    (H.edge s a b ↔ K.edge
      (candidateNewLeafTableMap H K m f v s)
      (candidateNewLeafTableMap H K m f v a)
      (candidateNewLeafTableMap H K m f v b))
  e5 : ∀ a b c : Nat,
    a ∈ countableDiaryFiniteSupport H (m + 1) →
    b ∈ countableDiaryFiniteSupport H (m + 1) →
    c ∈ countableDiaryFiniteSupport H (m + 1) →
    IsLeaf H a → IsLeaf H b → IsLeaf H c →
    a < b → b < c →
    (H.edge a b c ↔ K.edge
      (candidateNewLeafTableMap H K m f v a)
      (candidateNewLeafTableMap H K m f v b)
      (candidateNewLeafTableMap H K m f v c))

namespace FiniteNewLeafE2E3E5CandidateCondition

variable {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m v : Nat}

/-- Every reduced candidate is a genuine ORIGINAL finite candidate
once the source and target are full RoleDiary structures. The
nontrivial induced-edge field is supplied by the checked finite
E2/E3/E5 lemma and the functional S1 generator rows. -/
theorem toFull
    (DH : RoleDiary H) (DK : RoleDiary K)
    (C : FiniteNewLeafE2E3E5CandidateCondition H K F m f v) :
    FiniteNewLeafCandidateCondition H K F m f v where
  functional := C.functional
  leaf := C.leaf
  range := C.range
  ordered := C.ordered
  leaf_role := C.leaf_role
  one_split_role := C.one_split_role
  two_split_role := C.two_split_role
  induced_edge := functional_candidate_induced_of_E2_E3_E5
    DH DK F f m v C.functional C.ordered
    C.leaf_role C.one_split_role C.two_split_role
    C.e2 C.e3 C.e5

end FiniteNewLeafE2E3E5CandidateCondition

namespace FiniteNewLeafCandidateCondition

variable {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m v : Nat}

/-- Any original full candidate gives each smaller shape test
by specializing its complete induced edge/nonedge table. The
finite generator functionality already fixes the marker zero. -/
theorem toE2E3E5
    (C : FiniteNewLeafCandidateCondition H K F m f v) :
    FiniteNewLeafE2E3E5CandidateCondition H K F m f v := by
  have hMarker0 :
      candidateNewLeafTableMap H K m f v 0 = 0 := by
    change finiteGeneratorTableValue
      (candidateNewLeafGeneratorTable H K m f v) 0 = 0
    exact finiteGeneratorTableValue_eq_of_mem _
      C.functional 0 0
      (finiteLeafGeneratorTable_marker H K
        (countableDiaryLeafPrefix H (m + 1))
        (candidateLeafImage f m v) 0 (by omega))
  refine {
    functional := C.functional
    leaf := C.leaf
    range := C.range
    ordered := C.ordered
    leaf_role := C.leaf_role
    one_split_role := C.one_split_role
    two_split_role := C.two_split_role
    e2 := ?_
    e3 := ?_
    e5 := ?_
  }
  · intro s b hsS hbS hs hb hsb
    have hZeroS : 0 ∈ countableDiaryFiniteSupport H (m + 1) :=
      mem_finiteLeafMeetSupport_marker H
        (countableDiaryLeafPrefix H (m + 1)) 0 (by omega)
    have hZeroLt : 0 < s := by
      have hs3 := hs.1
      omega
    simpa only [hMarker0] using
      C.induced_edge 0 s b hZeroS hsS hbS hZeroLt hsb
  · intro s a b hsS haS hbS hs ha hb hsa hab
    exact C.induced_edge s a b hsS haS hbS hsa hab
  · intro a b c haS hbS hcS ha hb hc hab hbc
    exact C.induced_edge a b c haS hbS hcS hab hbc

end FiniteNewLeafCandidateCondition

/-- EXACT equivalence of the old and reduced candidate predicates.
No existing public criterion is altered or weakened. -/
theorem finiteCandidate_iff_reduced_E2_E3_E5
    {H K : Ordered3Graph Nat} (DH : RoleDiary H) (DK : RoleDiary K)
    (F f : Nat → Nat) (m v : Nat) :
    FiniteNewLeafCandidateCondition H K F m f v ↔
      FiniteNewLeafE2E3E5CandidateCondition H K F m f v := by
  constructor
  · exact fun C => C.toE2E3E5
  · exact fun C => C.toFull DH DK

/-- The existing exact fixed-new-leaf relative successor criterion
can therefore be checked with ONLY E2/E3/E5 edge/nonedge families,
plus the unchanged finite generator/role/order/range constraints.

The theorem is a criterion for a PROPOSED v; it does not find v. -/
theorem AdmissibleCofinalDiaryStage.relative_successor_iff_reduced_E2_E3_E5
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (hm : IsLeaf H m) (v : Nat) :
    (∃ g : Nat → Nat,
      AdmissibleCofinalDiaryStage H K F (m + 1) g ∧
      (∀ a : Nat, a ∈ countableDiaryLeafPrefix H m →
        g a = f a) ∧ g m = v) ↔
      FiniteNewLeafE2E3E5CandidateCondition H K F m f v := by
  exact (AdmissibleCofinalDiaryStage.relative_successor_iff_finite_candidate
    DH P hm v).trans (finiteCandidate_iff_reduced_E2_E3_E5
      DH DK F f m v)

end DiaryLeafPriority
end ThreeUniformDiaries
