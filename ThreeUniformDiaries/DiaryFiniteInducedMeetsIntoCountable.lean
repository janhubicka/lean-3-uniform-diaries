import ThreeUniformDiaries.DiaryFiniteGenericLeafUnavoidability
import ThreeUniformDiaries.DiaryFiniteInducedAllMeetTransport
import ThreeUniformDiaries.DiaryFiniteMixedAuxiliaryDichotomy
import ThreeUniformDiaries.DiaryFiniteEOnlySplitMeetDichotomy

/-!
# Mixed-meet transport of induced finite copies into countable diaries

The existing *finite target* mixed-meet proof uses only E1--E5
permitted edge shapes and the Devlin marker alternative; both hold
globally in an arbitrary countable full RoleDiary target.

A genuine finite leaf preembedding, induced on all source triples,
therefore preserves ALL numerical singleton and full pair-type
meets, including mixed split/leaf tuples and capped comparisons,
even when target enumeration levels are omitted. We reuse the
verified marker small-or-capped proofs without claiming arbitrary
old-cut type preservation.

Consequently the validated finite generic leaf-range theorem
can be upgraded to a full numerical meet embedding of the finite
source into the SAME countable target, still inside the ORIGINAL
generic embedding's leaf range.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Every ordered pair of countable nonmarker vertices either
includes a split or has a genuine Devlin marker-one/two edge. -/
theorem RoleDiary.split_or_pair_marker
    {T : Ordered3Graph Nat} (D : RoleDiary T)
    (a b : Nat) (ha3 : 3 ≤ a) (hab : a < b) :
    (IsDiarySplit T a ∨ IsDiarySplit T b) ∨
      (T.edge 1 a b ∨ T.edge 2 a b) := by
  have hb3 : 3 ≤ b := by omega
  rcases D.role_valid a ha3 with haLeaf | haOne | haTwo
  · rcases D.role_valid b hb3 with hbLeaf | hbOne | hbTwo
    · exact Or.inr
        (D.toPrediary.leaf_pair_has_marker a b hab haLeaf hbLeaf)
    · exact Or.inl (Or.inr (Or.inl hbOne))
    · exact Or.inl (Or.inr (Or.inr hbTwo))
  · exact Or.inl (Or.inl (Or.inl haOne))
  · exact Or.inl (Or.inl (Or.inr haTwo))

/-- The global E-only mixed pair auxiliary meet is small at
a marker or is exactly capped at its earlier first member. -/
theorem RoleDiary.mixed_auxMeet_small_or_capped
    {T : Ordered3Graph Nat} (D : RoleDiary T)
    (a b c d : Nat)
    (ha3 : 3 ≤ a) (hab : a < b)
    (hc3 : 3 ≤ c) (hcd : c < d)
    (hSomeMixed :
      (IsDiarySplit T a ∨ IsDiarySplit T b) ∨
      (IsDiarySplit T c ∨ IsDiarySplit T d)) :
    T.auxMeetLevel a b c d < 3 ∨
      T.auxMeetLevel a b c d = min a c := by
  exact E_mixed_auxMeet_small_or_capped D.permitted_edge
    a b c d ha3 hc3
    (D.split_or_pair_marker a b ha3 hab)
    (D.split_or_pair_marker c d hc3 hcd)
    hSomeMixed

variable {A T : Ordered3Graph Nat} {n k : Nat} {f : Nat → Nat}


theorem finite_induced_mixed_oneMeet_in_countable
    (PA : FiniteRolePrediaryBlock A n)
    (DT : RoleDiary T)
    (hf : StrictMono f)
    (h0 : f 0 = 0) (h1 : f 1 = 1) (h2 : f 2 = 2)
    (hInduced : ∀ a b c : Nat, a < b → b < c → c < n →
      (T.edge (f a) (f b) (f c) ↔ A.edge a b c))
    (u v : Nat) (hu3 : 3 ≤ u) (hun : u < n)
    (hv3 : 3 ≤ v) (hvn : v < n)
    (hSplit : IsDiarySplit A u ∨ IsDiarySplit A v) :
    T.oneMeetLevel (f u) (f v) =
      f (A.oneMeetLevel u v) := by
  have hRolesU := finite_induced_marker_roles_iff
    (A := A) (T := T) (n := n) (f := f)
    hf h0 h1 h2 hInduced u hu3 hun
  have hRolesV := finite_induced_marker_roles_iff
    (A := A) (T := T) (n := n) (f := f)
    hf h0 h1 h2 hInduced v hv3 hvn
  have hSrcU : IsLeaf A u ∨ IsDiarySplit A u := by
    rcases PA.role_valid u hu3 hun with huLeaf | huOne | huTwo
    · exact Or.inl huLeaf
    · exact Or.inr (Or.inl huOne)
    · exact Or.inr (Or.inr huTwo)
  have hSrcV : IsLeaf A v ∨ IsDiarySplit A v := by
    rcases PA.role_valid v hv3 hvn with hvLeaf | hvOne | hvTwo
    · exact Or.inl hvLeaf
    · exact Or.inr (Or.inl hvOne)
    · exact Or.inr (Or.inr hvTwo)
  have hDstU : IsLeaf T (f u) ∨ IsDiarySplit T (f u) := by
    rcases hSrcU with hLeaf | hSplit
    · exact Or.inl (hRolesU.1.mpr hLeaf)
    · rcases hSplit with hOne | hTwo
      · exact Or.inr (Or.inl (hRolesU.2.1.mpr hOne))
      · exact Or.inr (Or.inr (hRolesU.2.2.mpr hTwo))
  have hDstV : IsLeaf T (f v) ∨ IsDiarySplit T (f v) := by
    rcases hSrcV with hLeaf | hSplit
    · exact Or.inl (hRolesV.1.mpr hLeaf)
    · rcases hSplit with hOne | hTwo
      · exact Or.inr (Or.inl (hRolesV.2.1.mpr hOne))
      · exact Or.inr (Or.inr (hRolesV.2.2.mpr hTwo))
  have hDstSplit : IsDiarySplit T (f u) ∨ IsDiarySplit T (f v) := by
    rcases hSplit with hSu | hSv
    · rcases hSu with hOne | hTwo
      · exact Or.inl (Or.inl (hRolesU.2.1.mpr hOne))
      · exact Or.inl (Or.inr (hRolesU.2.2.mpr hTwo))
    · rcases hSv with hOne | hTwo
      · exact Or.inr (Or.inl (hRolesV.2.1.mpr hOne))
      · exact Or.inr (Or.inr (hRolesV.2.2.mpr hTwo))
  have hFu3 : 3 ≤ f u := by
    have hh := hf (show 2 < u by omega)
    rw [h2] at hh
    omega
  have hFv3 : 3 ≤ f v := by
    have hh := hf (show 2 < v by omega)
    rw [h2] at hh
    omega
  have hSrcCase := E_split_oneMeet_small_or_capped
    PA.permitted_edge u v hu3 hv3 hSrcU hSrcV hSplit
  have hDstCase := E_split_oneMeet_small_or_capped
    DT.permitted_edge (f u) (f v) hFu3 hFv3
      hDstU hDstV hDstSplit
  have hMarker : ∀ x : Nat, x < 3 → f x = x := by
    intro x hx
    exact fixed_three_markers h0 h1 h2 x hx
  have hPrefix : ∀ l : Nat, l ≤ 3 →
      (T.SameOneTypeBelow l (f u) (f v) ↔
        A.SameOneTypeBelow l u v) := by
    intro l hl
    exact marker_oneType_iff_of_induced
      (A := A) (T := T) (n := n) (f := f)
      h0 h1 h2 hInduced l u v hl hu3 hun hv3 hvn
  exact oneMeet_preserved_of_marker_dichotomy
    (A := A) (T := T) (f := f)
    hf hMarker u v hu3 hv3 hSrcCase hDstCase hPrefix

theorem finite_induced_mixed_auxMeet_in_countable
    (PA : FiniteRolePrediaryBlock A n)
    (DT : RoleDiary T)
    (Q : FiniteLeafPreembedding A T n k f)
    (hInduced : ∀ u v w : Nat, u < v → v < w → w < n →
      (T.edge (f u) (f v) (f w) ↔ A.edge u v w))
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha3 : 3 ≤ a) (han : a < n)
    (hbn : b < n)
    (hc3 : 3 ≤ c) (hcn : c < n)
    (hdn : d < n)
    (hSomeSplit :
      (IsDiarySplit A a ∨ IsDiarySplit A b) ∨
      (IsDiarySplit A c ∨ IsDiarySplit A d)) :
    T.auxMeetLevel (f a) (f b) (f c) (f d) =
      f (A.auxMeetLevel a b c d) := by
  have hb3 : 3 ≤ b := by omega
  have hd3 : 3 ≤ d := by omega
  have hF3 (u : Nat) (hu3 : 3 ≤ u) : 3 ≤ f u := by
    have hLt := Q.strictMono (show 2 < u by omega)
    rw [Q.marker_two] at hLt
    omega
  have hSplitImage : ∀ u : Nat, 3 ≤ u → u < n →
      IsDiarySplit A u → IsDiarySplit T (f u) := by
    intro u hu3 hun hs
    have hr := finite_induced_marker_roles_iff
      (A := A) (T := T) (n := n) (f := f)
      Q.strictMono Q.marker_zero Q.marker_one Q.marker_two
      hInduced u hu3 hun
    rcases hs with hOne | hTwo
    · exact Or.inl (hr.2.1.mpr hOne)
    · exact Or.inr (hr.2.2.mpr hTwo)
  have hTargetMixed :
      (IsDiarySplit T (f a) ∨ IsDiarySplit T (f b)) ∨
      (IsDiarySplit T (f c) ∨ IsDiarySplit T (f d)) := by
    rcases hSomeSplit with (ha | hb) | (hc | hd)
    · exact Or.inl (Or.inl (hSplitImage a ha3 han ha))
    · exact Or.inl (Or.inr (hSplitImage b hb3 hbn hb))
    · exact Or.inr (Or.inl (hSplitImage c hc3 hcn hc))
    · exact Or.inr (Or.inr (hSplitImage d hd3 hdn hd))
  have hSourceCase := PA.mixed_auxMeet_small_or_capped
    a b c d ha3 hab hbn hc3 hcd hdn hSomeSplit
  have hTargetCase := DT.mixed_auxMeet_small_or_capped
    (f a) (f b) (f c) (f d)
    (hF3 a ha3) (Q.strictMono hab)
    (hF3 c hc3) (Q.strictMono hcd)
    hTargetMixed
  have hMarker : ∀ t : Nat, t < 3 → f t = t := by
    intro t ht
    exact fixed_three_markers
      Q.marker_zero Q.marker_one Q.marker_two t ht
  have hPrefix : ∀ l : Nat, l ≤ 3 →
      (T.SameAuxTypeBelow l (f a) (f b) (f c) (f d) ↔
        A.SameAuxTypeBelow l a b c d) := by
    intro l hl
    exact marker_auxType_iff_of_induced
      (A := A) (T := T) (n := n) (f := f)
      Q.marker_zero Q.marker_one Q.marker_two
      hInduced l a b c d hl ha3 hab hbn hc3 hcd hdn
  exact auxMeet_preserved_of_marker_dichotomy
    (A := A) (T := T) (f := f)
    Q.strictMono hMarker a b c d ha3 hc3
    hSourceCase hTargetCase hPrefix

theorem finite_induced_all_oneMeet_in_countable
    (PA : FiniteRolePrediaryBlock A n)
    (DT : RoleDiary T)
    (Q : FiniteLeafPreembedding A T n k f)
    (hInduced : ∀ a b c : Nat, a < b → b < c → c < n →
      (T.edge (f a) (f b) (f c) ↔ A.edge a b c))
    (u v : Nat)
    (hu3 : 3 ≤ u) (hun : u < n)
    (hv3 : 3 ≤ v) (hvn : v < n) :
    T.oneMeetLevel (f u) (f v) =
      f (A.oneMeetLevel u v) := by
  by_cases hLeaves : IsLeaf A u ∧ IsLeaf A v
  · exact Q.leaf_oneMeet u v hu3 hun hv3 hvn hLeaves.1 hLeaves.2
  · have hSplit := PA.pair_contains_split_of_not_both_leaf
      u v hu3 hun hv3 hvn hLeaves
    exact finite_induced_mixed_oneMeet_in_countable
      PA DT Q.strictMono
      Q.marker_zero Q.marker_one Q.marker_two
      hInduced u v hu3 hun hv3 hvn hSplit

theorem finite_induced_all_twoMeet_in_countable
    (PA : FiniteRolePrediaryBlock A n)
    (DT : RoleDiary T)
    (Q : FiniteLeafPreembedding A T n k f)
    (hInduced : ∀ u v w : Nat, u < v → v < w → w < n →
      (T.edge (f u) (f v) (f w) ↔ A.edge u v w))
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha3 : 3 ≤ a) (han : a < n)
    (hb3 : 3 ≤ b) (hbn : b < n)
    (hc3 : 3 ≤ c) (hcn : c < n)
    (hd3 : 3 ≤ d) (hdn : d < n) :
    T.twoMeetLevel (f a) (f b) (f c) (f d) =
      f (A.twoMeetLevel a b c d) := by
  by_cases hAllLeaves :
      (IsLeaf A a ∧ IsLeaf A b) ∧
      (IsLeaf A c ∧ IsLeaf A d)
  · exact Q.leaf_twoMeet a b c d hab hcd
      ha3 han hb3 hbn hc3 hcn hd3 hdn
      hAllLeaves.1.1 hAllLeaves.1.2
      hAllLeaves.2.1 hAllLeaves.2.2
  · have hSomeMixed :
        (IsDiarySplit A a ∨ IsDiarySplit A b) ∨
        (IsDiarySplit A c ∨ IsDiarySplit A d) := by
      by_cases hAB : IsLeaf A a ∧ IsLeaf A b
      · have hCD : ¬ (IsLeaf A c ∧ IsLeaf A d) := by
          intro hc
          exact hAllLeaves ⟨hAB,hc⟩
        exact Or.inr (PA.pair_contains_split_of_not_both_leaf
          c d hc3 hcn hd3 hdn hCD)
      · exact Or.inl (PA.pair_contains_split_of_not_both_leaf
          a b ha3 han hb3 hbn hAB)
    have hFirst := finite_induced_all_oneMeet_in_countable
      PA DT Q hInduced a c ha3 han hc3 hcn
    have hSecond := finite_induced_all_oneMeet_in_countable
      PA DT Q hInduced b d hb3 hbn hd3 hdn
    have hAux := finite_induced_mixed_auxMeet_in_countable
      PA DT Q hInduced a b c d
      hab hcd ha3 han hbn hc3 hcn hdn hSomeMixed
    have hMapMin : ∀ x y : Nat,
        min (f x) (f y) = f (min x y) := by
      intro x y
      have hMon := Q.strictMono.monotone
      rcases le_total x y with hxy | hyx
      · rw [min_eq_left (hMon hxy), min_eq_left hxy]
      · rw [min_eq_right (hMon hyx), min_eq_right hyx]
    rw [T.twoMeetLevel_eq_min (f a) (f b) (f c) (f d)
        (Q.strictMono hab) (Q.strictMono hcd),
      A.twoMeetLevel_eq_min a b c d hab hcd]
    rw [hFirst,hSecond,hAux]
    simp only [hMapMin]


/-- Inducedness upgrades a genuine finite leaf preembedding into
any countable full diary to a FULL finite meet embedding. -/
theorem FiniteLeafPreembedding.toMeetEmbedding_into_countable
    (DA : FiniteRoleDiaryBlock A n)
    (DT : RoleDiary T)
    (P : FiniteLeafPreembedding A T n k f)
    (hInduced : ∀ a b c : Nat, a < b → b < c → c < n →
      (T.edge (f a) (f b) (f c) ↔ A.edge a b c)) :
    FiniteMeetEmbedding A T n f := by
  refine {
    strictMono := P.strictMono
    marker_zero := P.marker_zero
    marker_one := P.marker_one
    marker_two := P.marker_two
    edge_iff := hInduced
    leaf_iff := ?_
    oneSplit_iff := ?_
    twoSplit_iff := ?_
    oneMeet := ?_
    twoMeet := ?_
  }
  · intro u hu3 hun
    exact (P.role_iff u hu3 hun).1
  · intro u hu3 hun
    exact (P.role_iff u hu3 hun).2.1
  · intro u hu3 hun
    exact (P.role_iff u hu3 hun).2.2
  · intro u v hu3 hun hv3 hvn
    exact finite_induced_all_oneMeet_in_countable
      DA.prediary DT P hInduced u v hu3 hun hv3 hvn
  · intro a b c d hab hcd ha3 han hb3 hbn hc3 hcn hd3 hdn
    exact finite_induced_all_twoMeet_in_countable
      DA.prediary DT P hInduced a b c d hab hcd
      ha3 han hb3 hbn hc3 hcn hd3 hdn

/-- Stronger finite lower-bound assertion using the manuscript's
actual full diary-embedding notion, not just a leaf preembedding.
The same specified generic image still contains all source leaves. -/
theorem exists_finiteDiary_full_embedding_in_generic_leaf_range
    {A T : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph T)
    (hFleaf : ∀ u, IsLeaf T (F u))
    (DT : RoleDiary T) :
    ∃ f : Nat → Nat,
      FiniteMeetEmbedding A T n f ∧
      (∀ u : Nat, 3 ≤ u → u < n → IsLeaf A u →
        ∃ t : Nat, f u = F t) := by
  obtain ⟨m,f,P,hInduced,hLeafRange⟩ :=
    exists_finiteDiary_copy_in_generic_leaf_range
      DA G F hFleaf DT
  exact ⟨f, P.toMeetEmbedding_into_countable DA DT hInduced,
    hLeafRange⟩

end DiaryLeafPriority
end ThreeUniformDiaries
