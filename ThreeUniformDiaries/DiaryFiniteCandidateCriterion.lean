import ThreeUniformDiaries.DiaryFiniteCandidateTableNecessity
import ThreeUniformDiaries.DiaryFiniteLeafMeetOnlySelectedLeaves

/-!
# Exact finite criterion for one prescribed fresh diary leaf image

Fix a valid old finite stage and a proposed target image v for a new
source leaf m. The finite generator table forces ALL images on the
next support. Its functionality, finite order/role/induced-edge tests,
and membership of v in the prescribed target leaf range are jointly
equivalent to the existence of a genuine relative successor with
g(m)=v.

This is deliberately a fixed-CANDIDATE equivalence. It does NOT
assert that some suitable v belongs to the prescribed range and
does not imply unrestricted countable diary unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The unique proposed total map obtained from the finite table
if its source rows are compatible. Outside the support it is
arbitrary (zero when no generator row is available). -/
noncomputable def candidateNewLeafTableMap
    (H K : Ordered3Graph Nat) (m : Nat)
    (f : Nat → Nat) (v u : Nat) : Nat :=
  finiteGeneratorTableValue
    (candidateNewLeafGeneratorTable H K m f v) u

/-- The finite checks remaining once v is prescribed. They
inspect only the finite generated support and its finite table.
The separate range membership clause can be given by an explicit
witness t such that v=F(t), not by assuming decidability of F[Nat]. -/
structure FiniteNewLeafCandidateCondition
    (H K : Ordered3Graph Nat) (F : Nat → Nat)
    (m : Nat) (f : Nat → Nat) (v : Nat) : Prop where
  functional :
    FiniteGeneratorTableFunctional
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
    IsLeaf H a →
    IsLeaf K (candidateNewLeafTableMap H K m f v a)
  one_split_role : ∀ a : Nat,
    a ∈ countableDiaryFiniteSupport H (m + 1) →
    IsOneSplit H a →
    IsOneSplit K (candidateNewLeafTableMap H K m f v a)
  two_split_role : ∀ a : Nat,
    a ∈ countableDiaryFiniteSupport H (m + 1) →
    IsTwoSplit H a →
    IsTwoSplit K (candidateNewLeafTableMap H K m f v a)
  induced_edge : ∀ a b c : Nat,
    a ∈ countableDiaryFiniteSupport H (m + 1) →
    b ∈ countableDiaryFiniteSupport H (m + 1) →
    c ∈ countableDiaryFiniteSupport H (m + 1) →
    a < b → b < c →
    (H.edge a b c ↔
      K.edge
        (candidateNewLeafTableMap H K m f v a)
        (candidateNewLeafTableMap H K m f v b)
        (candidateNewLeafTableMap H K m f v c))

namespace FiniteNewLeafCandidateCondition

variable {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m v : Nat}

/-- For every selected leaf, a functional table uses its
explicitly prescribed leaf image rather than a separate choice. -/
theorem chosen_selected_leaf
    (C : FiniteNewLeafCandidateCondition H K F m f v)
    (a : Nat) (ha : a ∈ countableDiaryLeafPrefix H (m + 1)) :
    candidateNewLeafTableMap H K m f v a =
      candidateLeafImage f m v a := by
  change finiteGeneratorTableValue
      (candidateNewLeafGeneratorTable H K m f v) a =
      candidateLeafImage f m v a
  exact finiteGeneratorTableValue_eq_of_mem
    _ C.functional a _
    (finiteLeafGeneratorTable_leaf
      H K (countableDiaryLeafPrefix H (m + 1))
      (candidateLeafImage f m v) a ha)

end FiniteNewLeafCandidateCondition

namespace AdmissibleCofinalDiaryStage

variable {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m v : Nat}

/-- A true prescribed-leaf successor satisfies all finite tests
on the generator table. No extra diary axiom is required here
beyond those in the given admissible stage. -/
theorem relative_successor_implies_finite_candidate
    {g : Nat → Nat}
    (Q : AdmissibleCofinalDiaryStage H K F (m + 1) g)
    (hm : IsLeaf H m)
    (hKeep : ∀ a : Nat, a ∈ countableDiaryLeafPrefix H m →
      g a = f a)
    (hNew : g m = v) :
    FiniteNewLeafCandidateCondition H K F m f v := by
  have hmSelected : m ∈ countableDiaryLeafPrefix H (m + 1) :=
    (mem_countableDiaryLeafPrefix_iff H (m + 1) m).mpr
      ⟨hm.1,by omega,hm⟩
  have hmSupported : m ∈ countableDiaryFiniteSupport H (m + 1) :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H (m + 1)) m hmSelected
  have hFunctional :=
    Q.relative_successor_generator_table_functional hKeep hNew
  have hVal (u : Nat)
      (hu : u ∈ countableDiaryFiniteSupport H (m + 1)) :
      candidateNewLeafTableMap H K m f v u = g u := by
    exact Q.relative_successor_agrees_with_table hKeep hNew u hu
  refine {
    functional := hFunctional
    leaf := by simpa only [hNew] using Q.leaf_role m hmSupported hm
    range := by simpa only [hNew] using Q.leaf_range m hmSupported hm
    ordered := ?_
    leaf_role := ?_
    one_split_role := ?_
    two_split_role := ?_
    induced_edge := ?_
  }
  · intro a b ha hb hab
    rw [hVal a ha,hVal b hb]
    exact Q.ordered a b ha hb hab
  · intro a ha hLeaf
    rw [hVal a ha]
    exact Q.leaf_role a ha hLeaf
  · intro a ha hOne
    rw [hVal a ha]
    exact Q.one_split_role a ha hOne
  · intro a ha hTwo
    rw [hVal a ha]
    exact Q.two_split_role a ha hTwo
  · intro a b c ha hb hc hab hbc
    rw [hVal a ha,hVal b hb,hVal c hc]
    exact Q.induced_edge a b c ha hb hc hab hbc

/-- The reverse implication is the substantive finite-table
construction. All role/order/edge tests are assumed for the
FINITE table-selected map; all numerical meet tests follow
from its generator rows, including the diagonal one-meet case.

The full diary axiom is used only to prove that generated support
contains no unselected leaves, so its old leaf range is exhaustive. -/
theorem finite_candidate_implies_relative_successor
    (DH : RoleDiary H)
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (hm : IsLeaf H m)
    (C : FiniteNewLeafCandidateCondition H K F m f v) :
    ∃ g : Nat → Nat,
      AdmissibleCofinalDiaryStage H K F (m + 1) g ∧
      (∀ a : Nat, a ∈ countableDiaryLeafPrefix H m →
        g a = f a) ∧ g m = v := by
  classical
  let L := countableDiaryLeafPrefix H (m + 1)
  let Lold := countableDiaryLeafPrefix H m
  let T := candidateNewLeafGeneratorTable H K m f v
  let q := candidateLeafImage f m v
  let g : Nat → Nat := candidateNewLeafTableMap H K m f v
  have hSelectedLeaf : ∀ a : Nat, a ∈ L → IsLeaf H a := by
    intro a ha
    exact ((mem_countableDiaryLeafPrefix_iff H (m + 1) a).mp ha).2.2
  have hSelectedSupport : ∀ a : Nat, a ∈ L →
      a ∈ countableDiaryFiniteSupport H (m + 1) := by
    intro a ha
    exact mem_finiteLeafMeetSupport_leaf H L a ha
  have hOnlySelected : ∀ a : Nat,
      a ∈ countableDiaryFiniteSupport H (m + 1) →
      IsLeaf H a → a ∈ L := by
    intro a ha hLeaf
    exact finiteLeafMeetSupport_leaf_mem_L DH hSelectedLeaf ha hLeaf
  have hQLeaf : ∀ a : Nat, a ∈ L → g a = q a := by
    intro a ha
    exact C.chosen_selected_leaf a ha
  have hOld : ∀ a : Nat, a ∈ Lold → g a = f a := by
    intro a ha
    have haNew : a ∈ L :=
      (countableDiaryLeafPrefix_mono H m (m + 1) (by omega)) ha
    have ham : a ≠ m := by
      have hlt := ((mem_countableDiaryLeafPrefix_iff H m a).mp ha).2.1
      omega
    calc
      g a = q a := hQLeaf a haNew
      _ = f a := by simp [q,candidateLeafImage,ham]
  have hmSelected : m ∈ L :=
    (mem_countableDiaryLeafPrefix_iff H (m + 1) m).mpr
      ⟨hm.1,by omega,hm⟩
  have hNew : g m = v := by
    calc
      g m = q m := hQLeaf m hmSelected
      _ = v := by simp [q,candidateLeafImage]
  have hMarker (i : Nat) (hi : i < 3) : g i = i := by
    exact finiteGeneratorTableValue_eq_of_mem T C.functional i i
      (finiteLeafGeneratorTable_marker H K L q i hi)
  let Q : AdmissibleCofinalDiaryStage H K F (m + 1) g := {
    ordered := C.ordered
    marker_zero := hMarker 0 (by omega)
    marker_one := hMarker 1 (by omega)
    marker_two := hMarker 2 (by omega)
    leaf_role := C.leaf_role
    one_split_role := C.one_split_role
    two_split_role := C.two_split_role
    induced_edge := C.induced_edge
    leaf_oneMeet := by
      intro a b ha hb hLa hLb
      have haL : a ∈ L := hOnlySelected a ha hLa
      have hbL : b ∈ L := hOnlySelected b hb hLb
      by_cases hab : a = b
      · subst b
        simp only [Ordered3Graph.oneMeetLevel_self]
      · have hRow :
            (H.oneMeetLevel a b,
              K.oneMeetLevel (q a) (q b)) ∈ T :=
          finiteLeafGeneratorTable_oneMeet H K L q
            a b haL hbL hab
        have hValue :
            g (H.oneMeetLevel a b) =
              K.oneMeetLevel (q a) (q b) :=
          finiteGeneratorTableValue_eq_of_mem T C.functional _ _ hRow
        calc
          K.oneMeetLevel (g a) (g b) =
              K.oneMeetLevel (q a) (q b) := by
                rw [hQLeaf a haL,hQLeaf b hbL]
          _ = g (H.oneMeetLevel a b) := hValue.symm
    leaf_twoMeet := by
      intro a b c d ha hb hc hd hab hcd hLa hLb hLc hLd
      have haL : a ∈ L := hOnlySelected a ha hLa
      have hbL : b ∈ L := hOnlySelected b hb hLb
      have hcL : c ∈ L := hOnlySelected c hc hLc
      have hdL : d ∈ L := hOnlySelected d hd hLd
      have hRow :
          (H.twoMeetLevel a b c d,
            K.twoMeetLevel (q a) (q b) (q c) (q d)) ∈ T :=
        finiteLeafGeneratorTable_twoMeet H K L q
          a b c d haL hbL hcL hdL hab hcd
      have hValue :
          g (H.twoMeetLevel a b c d) =
            K.twoMeetLevel (q a) (q b) (q c) (q d) :=
        finiteGeneratorTableValue_eq_of_mem T C.functional _ _ hRow
      calc
        K.twoMeetLevel (g a) (g b) (g c) (g d) =
            K.twoMeetLevel (q a) (q b) (q c) (q d) := by
              rw [hQLeaf a haL,hQLeaf b hbL,
                hQLeaf c hcL,hQLeaf d hdL]
        _ = g (H.twoMeetLevel a b c d) := hValue.symm
    leaf_range := by
      intro a ha hLeaf
      have haL : a ∈ L := hOnlySelected a ha hLeaf
      by_cases ham : a = m
      · subst a
        obtain ⟨t,ht⟩ := C.range
        exact ⟨t, hNew.trans ht⟩
      · obtain ⟨ha3,hamNew,_⟩ :=
          (mem_countableDiaryLeafPrefix_iff H (m + 1) a).mp haL
        have haOld : a ∈ Lold :=
          (mem_countableDiaryLeafPrefix_iff H m a).mpr
            ⟨ha3,by omega,hLeaf⟩
        have haSupported : a ∈ countableDiaryFiniteSupport H m :=
          mem_finiteLeafMeetSupport_leaf H Lold a haOld
        obtain ⟨t,ht⟩ := P.leaf_range a haSupported hLeaf
        exact ⟨t,(hOld a haOld).trans ht⟩
  }
  exact ⟨g,Q,hOld,hNew⟩

/-- Exact fixed-candidate finite realization criterion.

This equivalence genuinely eliminates arbitrary Nat-valued
successor maps from the fixed-v search. The right side is a
finite generator functionality test and finite support geometry
test, together with prescribed-range membership. No theorem
here ensures a suitable v exists at each countable leaf stage. -/
theorem relative_successor_iff_finite_candidate
    (DH : RoleDiary H)
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (hm : IsLeaf H m) (v : Nat) :
    (∃ g : Nat → Nat,
      AdmissibleCofinalDiaryStage H K F (m + 1) g ∧
      (∀ a : Nat, a ∈ countableDiaryLeafPrefix H m →
        g a = f a) ∧ g m = v) ↔
    FiniteNewLeafCandidateCondition H K F m f v := by
  constructor
  · rintro ⟨g,Q,hKeep,hNew⟩
    exact Q.relative_successor_implies_finite_candidate hm hKeep hNew
  · intro C
    exact finite_candidate_implies_relative_successor DH P hm C

end AdmissibleCofinalDiaryStage
end DiaryLeafPriority
end ThreeUniformDiaries
