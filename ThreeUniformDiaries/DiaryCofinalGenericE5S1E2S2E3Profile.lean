import ThreeUniformDiaries.DiaryCofinalGenericE5RootS1E2Sign
import ThreeUniformDiaries.DiaryTwoSplitWitnessClasses
import ThreeUniformDiaries.DiaryFiniteLeafMeetSupport

/-!
# Track A: cofinal joint S2 pair profiles and actual E3 signs with E5/S1/E2

The previous theorem gives ONE cofinally recurring complete old-pair
E5 pattern, full singleton colour, and exact numeric finite-root
S1 meet / E2 sign vector, witnessed by the SAME actual leaves
of one prescribed unordered induced generic true-leaf range.

For an arbitrary finite old target leaf family W, also record
the FULL two-type meet of each ordered old pair (a,b) in W
with each new pair (w,v) where w is in W and v is the selected
new target leaf. Every such capped pair-meet level is at most
w and therefore belongs to one FINITE numeric palette.
Finite downward choice stabilizes this ENTIRE S2 cross-pair
profile while preserving all of the existing joint conditions.

The complete target RoleDiary S2 axiom classifies every stabilized
coordinate as a leaf cap, marker 1 or genuine two-split. For each
genuine two-split, the checked V2 two-sided witness theorem
forces the new pair (w,v) to have E3 incidence OPPOSITE to
the already fixed old pair (a,b) at that split. Thus all
genuine-cross E3 signs are fixed on the same cofinal fibre.

The numerical S1/S2 profile is existentially selected, not the
source-required profile of a prescribed old diary stage.
No new generator-table functionality, target order reserve,
persistent image or unconditional diary unavoidability follows.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Complete numerical cross-S2 meet vector for each ordered
old target leaf pair and each possible first leaf of a new pair.
It is genuinely finite since every capped meet is bounded
by the fixed old root. -/
abbrev FiniteRootCrossPairMeetProfile (W : Finset Nat) :=
  {ab : Nat × Nat // ab ∈ finiteOrderedLeafPairs W} →
  {w : Nat // w ∈ W} →
  Fin ((W.sup (fun x : Nat => x)) + 1)

/-- A fixed, complete cross-S2 numeric profile can be selected
cofinally on the SAME target leaves satisfying the prescribed
old E5 incidence table, a fixed full mixed singleton colour,
and all finite-root S1 and E2 conditions.

Every S2 coordinate is guaranteed to be one of the exact
full-diary cap, marker or genuine-two-split alternatives.
These alternatives are not assumed to be the ones demanded
by any particular source diary. -/
theorem RoleDiary.exists_cofinal_generic_joint_E5_S1_E2_and_S2_profile
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (W : Finset Nat) (hRoots : ∀ w : Nat, w ∈ W → IsLeaf K w)
    (B : Nat) (chi : Nat → Nat → Bool) :
    ∃ c : Fin B → Fin B → Bool,
      ∃ p : FiniteRootMeetProfile W,
        ∃ q : FiniteRootCrossPairMeetProfile W,
          (∀ w : {w : Nat // w ∈ W},
            IsOneSplit K (p w).val ∧ (p w).val < w.val) ∧
          (∀ ab : {ab : Nat × Nat // ab ∈ finiteOrderedLeafPairs W},
            ∀ w : {w : Nat // w ∈ W},
              (q ab w).val = min ab.val.1 w.val ∨
              (q ab w).val = 1 ∨ IsTwoSplit K (q ab w).val) ∧
          (∀ N M : Nat, ∃ t : Nat,
            N ≤ t ∧ M < F t ∧ B < F t ∧ IsLeaf K (F t) ∧
            DiaryLowerBoundColors.singletonColour K B (F t) = c ∧
            (∀ i j : Nat, F i < F j → F j < B →
              (K.edge (F i) (F j) (F t) ↔
                chi (F i) (F j) = true)) ∧
            (∀ w : {w : Nat // w ∈ W},
              K.oneMeetLevel w.val (F t) = (p w).val ∧
              (K.edge 0 (p w).val (F t) ↔
                ¬ K.edge 0 (p w).val w.val)) ∧
            (∀ ab : {ab : Nat × Nat // ab ∈ finiteOrderedLeafPairs W},
              ∀ w : {w : Nat // w ∈ W},
                K.twoMeetLevel ab.val.1 ab.val.2 w.val (F t) =
                  (q ab w).val)) := by
  classical
  obtain ⟨c, p, hpRoles, hOld⟩ :=
    DK.exists_cofinal_generic_E5_pattern_and_finiteRoot_S1_E2
      G F hFLeaf W hRoots B chi
  let T := W.sup (fun w : Nat => w)
  let pairProfile : Nat → FiniteRootCrossPairMeetProfile W :=
    fun t ab w =>
      ⟨K.twoMeetLevel ab.val.1 ab.val.2 w.val (F t), by
        have hCap :
            K.twoMeetLevel ab.val.1 ab.val.2 w.val (F t) ≤ w.val :=
          (K.twoMeetLevel_le_min
            ab.val.1 ab.val.2 w.val (F t)).trans
            (min_le_right _ _)
        have hw : w.val ≤ T :=
          Finset.le_sup (f := fun x : Nat => x) w.property
        omega⟩
  let R : FiniteRootCrossPairMeetProfile W → Nat → Prop :=
    fun q N => ∃ t : Nat,
      N ≤ t ∧ N < F t ∧ T < F t ∧ B < F t ∧
      IsLeaf K (F t) ∧
      DiaryLowerBoundColors.singletonColour K B (F t) = c ∧
      (∀ i j : Nat, F i < F j → F j < B →
        (K.edge (F i) (F j) (F t) ↔
          chi (F i) (F j) = true)) ∧
      (∀ w : {w : Nat // w ∈ W},
        K.oneMeetLevel w.val (F t) = (p w).val ∧
        (K.edge 0 (p w).val (F t) ↔
          ¬ K.edge 0 (p w).val w.val)) ∧
      pairProfile t = q
  have hDown : ∀ q : FiniteRootCrossPairMeetProfile W,
      ∀ N M : Nat, M ≤ N → R q N → R q M := by
    intro q N M hMN
    rintro ⟨t, htN, hNumN, hT, hB, htLeaf,
      htColour, htPattern, htRoots, hq⟩
    exact ⟨t, hMN.trans htN,
      lt_of_le_of_lt hMN hNumN,
      hT, hB, htLeaf, htColour, htPattern, htRoots, hq⟩
  have hCover : ∀ N : Nat,
      ∃ q : FiniteRootCrossPairMeetProfile W,
        q ∈ (Finset.univ : Finset (FiniteRootCrossPairMeetProfile W)) ∧
        R q N := by
    intro N
    obtain ⟨t, htN, hNum, hB, htLeaf, htColour,
      htPattern, htRoots⟩ := hOld N (max N T)
    have hNumN : N < F t :=
      lt_of_le_of_lt (le_max_left N T) hNum
    have hNumT : T < F t :=
      lt_of_le_of_lt (le_max_right N T) hNum
    exact ⟨pairProfile t, Finset.mem_univ _, t, htN,
      hNumN, hNumT, hB, htLeaf, htColour,
      htPattern, htRoots, rfl⟩
  obtain ⟨q, _hq, hAll⟩ :=
    finite_choice_persistent_of_downward_type
      (Finset.univ : Finset (FiniteRootCrossPairMeetProfile W))
      R hDown hCover
  have hS2Role
      (ab : {ab : Nat × Nat // ab ∈ finiteOrderedLeafPairs W})
      (w : {w : Nat // w ∈ W}) :
      (q ab w).val = min ab.val.1 w.val ∨
      (q ab w).val = 1 ∨ IsTwoSplit K (q ab w).val := by
    obtain ⟨t, _htN, _htM, hT, _hB, htLeaf,
      _htColour, _htPattern, _htRoots, hPair⟩ := hAll (T + 1)
    have hWBound : w.val ≤ T :=
      Finset.le_sup (f := fun x : Nat => x) w.property
    have hwv : w.val < F t := by omega
    have hOrderedPair : ab.val.1 < ab.val.2 :=
      (Finset.mem_filter.mp ab.property).2
    have hPairMem :
        (ab.val.1, ab.val.2) ∈ W.product W :=
      (Finset.mem_filter.mp ab.property).1
    obtain ⟨haMem, hbMem⟩ := Finset.mem_product.mp hPairMem
    have hA : IsLeaf K ab.val.1 := hRoots ab.val.1 haMem
    have hBLeaf : IsLeaf K ab.val.2 := hRoots ab.val.2 hbMem
    have hW : IsLeaf K w.val := hRoots w.val w.property
    have hMeet :
        K.twoMeetLevel ab.val.1 ab.val.2 w.val (F t) =
          (q ab w).val := by
      have h := congrArg
        (fun z : FiniteRootCrossPairMeetProfile W => (z ab w).val)
        hPair
      change K.twoMeetLevel ab.val.1 ab.val.2 w.val (F t) =
        (q ab w).val at h
      exact h
    have hCases := DK.pair_meets
      ab.val.1 ab.val.2 w.val (F t)
      hOrderedPair hwv hA hBLeaf hW htLeaf
    rw [hMeet] at hCases
    exact hCases
  refine ⟨c, p, q, hpRoles, hS2Role, ?_⟩
  intro N M
  obtain ⟨t, ht, hImage, _hT, hB, htLeaf, htColour,
    htPattern, htRoots, hPair⟩ := hAll (max N M)
  refine ⟨t, (le_max_left _ _).trans ht,
    lt_of_le_of_lt (le_max_right _ _) hImage,
    hB, htLeaf, htColour, htPattern, htRoots, ?_⟩
  intro ab w
  have h := congrArg
    (fun z : FiniteRootCrossPairMeetProfile W => (z ab w).val)
    hPair
  change K.twoMeetLevel ab.val.1 ab.val.2 w.val (F t) =
    (q ab w).val at h
  exact h

/-- Strengthening: at every stabilized cross-S2 coordinate that is
a TRUE target two-split, the new pair (w,v) is on the E3 branch
opposite to the fixed old pair (a,b). This is the actual V2
witness property of the full target RoleDiary, not an extra
independence assumption.

Cap and marker-1 coordinates impose no artificial E3 branch. -/
theorem RoleDiary.exists_cofinal_generic_joint_E5_S1_E2_S2_E3
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (W : Finset Nat) (hRoots : ∀ w : Nat, w ∈ W → IsLeaf K w)
    (B : Nat) (chi : Nat → Nat → Bool) :
    ∃ c : Fin B → Fin B → Bool,
      ∃ p : FiniteRootMeetProfile W,
        ∃ q : FiniteRootCrossPairMeetProfile W,
          (∀ w : {w : Nat // w ∈ W},
            IsOneSplit K (p w).val ∧ (p w).val < w.val) ∧
          (∀ ab : {ab : Nat × Nat // ab ∈ finiteOrderedLeafPairs W},
            ∀ w : {w : Nat // w ∈ W},
              (q ab w).val = min ab.val.1 w.val ∨
              (q ab w).val = 1 ∨ IsTwoSplit K (q ab w).val) ∧
          (∀ N M : Nat, ∃ t : Nat,
            N ≤ t ∧ M < F t ∧ B < F t ∧ IsLeaf K (F t) ∧
            DiaryLowerBoundColors.singletonColour K B (F t) = c ∧
            (∀ i j : Nat, F i < F j → F j < B →
              (K.edge (F i) (F j) (F t) ↔
                chi (F i) (F j) = true)) ∧
            (∀ w : {w : Nat // w ∈ W},
              K.oneMeetLevel w.val (F t) = (p w).val ∧
              (K.edge 0 (p w).val (F t) ↔
                ¬ K.edge 0 (p w).val w.val)) ∧
            (∀ ab : {ab : Nat × Nat // ab ∈ finiteOrderedLeafPairs W},
              ∀ w : {w : Nat // w ∈ W},
                K.twoMeetLevel ab.val.1 ab.val.2 w.val (F t) =
                  (q ab w).val ∧
                (IsTwoSplit K (q ab w).val →
                  (K.edge (q ab w).val w.val (F t) ↔
                    ¬ K.edge (q ab w).val ab.val.1 ab.val.2)))) := by
  classical
  obtain ⟨c, p, q, hOneRoles, hTwoRoles, hAll⟩ :=
    DK.exists_cofinal_generic_joint_E5_S1_E2_and_S2_profile
      G F hFLeaf W hRoots B chi
  refine ⟨c, p, q, hOneRoles, hTwoRoles, ?_⟩
  intro N M
  let T := W.sup (fun w : Nat => w)
  obtain ⟨t, htN, hMt, hB, htLeaf,
      htColour, htPattern, htRoot, htPair⟩ :=
    hAll N (max M T)
  have hM : M < F t :=
    lt_of_le_of_lt (le_max_left M T) hMt
  refine ⟨t, htN, hM, hB, htLeaf,
    htColour, htPattern, htRoot, ?_⟩
  intro ab w
  have hMeet := htPair ab w
  refine ⟨hMeet, ?_⟩
  intro hSplit
  have hPairMem :
      (ab.val.1, ab.val.2) ∈ W.product W :=
    (Finset.mem_filter.mp ab.property).1
  obtain ⟨haMem, _hbMem⟩ := Finset.mem_product.mp hPairMem
  have hA : IsLeaf K ab.val.1 := hRoots ab.val.1 haMem
  have hW : IsLeaf K w.val := hRoots w.val w.property
  have hCapA : (q ab w).val ≤ ab.val.1 := by
    have hCap :=
      (K.twoMeetLevel_le_min
        ab.val.1 ab.val.2 w.val (F t)).trans
        (min_le_left _ _)
    rw [hMeet] at hCap
    exact hCap
  have hCapW : (q ab w).val ≤ w.val := by
    have hCap :=
      (K.twoMeetLevel_le_min
        ab.val.1 ab.val.2 w.val (F t)).trans
        (min_le_right _ _)
    rw [hMeet] at hCap
    exact hCap
  have hNeA : (q ab w).val ≠ ab.val.1 := by
    intro hEq
    have hBad : IsTwoSplit K ab.val.1 := by
      simpa only [hEq] using hSplit
    exact hA.2.2 hBad.2.2
  have hNeW : (q ab w).val ≠ w.val := by
    intro hEq
    have hBad : IsTwoSplit K w.val := by
      simpa only [hEq] using hSplit
    exact hW.2.2 hBad.2.2
  have hBelowA : (q ab w).val < ab.val.1 := by omega
  have hBelowW : (q ab w).val < w.val := by omega
  have hOpp :
      ¬ (K.edge (q ab w).val ab.val.1 ab.val.2 ↔
          K.edge (q ab w).val w.val (F t)) :=
    DK.twoSplit_witness_opposite_incidence
      (q ab w).val ab.val.1 ab.val.2 w.val (F t)
      hSplit hBelowA hBelowW hMeet
  tauto

end DiaryLeafPriority
end ThreeUniformDiaries
