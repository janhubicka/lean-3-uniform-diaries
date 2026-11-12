import ThreeUniformDiaries.DiaryCofinalGenericE5S1E2S2E3Profile

/-!
# Track A: complete the cofinal mixed S2/E3 profile for old-new versus old-new pairs

The already checked joint profile theorem fixes a complete old-pair
E5 pattern, one complete finite singleton colour, all S1/E2 data
against finitely many genuine roots W, and the exact capped S2
pair-meets (a,b) versus (w,v) and their genuine E3 branch bits.

This module fills the MISSING second new pair family: for every
two distinct roots a<b, record the literal S2 meet of (a,v) and
(b,v), where v is the SAME genuinely late target leaf.

These levels are capped by a and hence form a FINITE palette.
A second finite downward-choice argument stabilizes the entire
new-new S2 vector without losing any previous E5/S1/E2/cross-S2/E3
condition. The target full S2 axiom classifies each value as a leaf
cap, marker 1, or genuine two-split. At a genuine two-split, V2
forces the actual E3 bits of (a,v) and (b,v) to be opposite.

Together with old-old/old-old (already fixed), old-old/old-new
(the previous theorem), and the diagonal new-pair comparison
(capped by its first leaf), this accounts for all shapes of
full pair-meet records after ONE new selected leaf.

Everything remains an EXISTENTIALLY CHOSEN target profile, not a
source-prescribed generator table. The theorem does NOT establish
functionality, a reserved relative successor, future spacing,
persistent leaf image or unconditional diary unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Numerical meet levels of new leaf pairs (a,v) and (b,v)
for every ordered pair a<b of distinct finite old roots.
Every value is bounded by the old root a. -/
abbrev FiniteRootNewNewPairMeetProfile (W : Finset Nat) :=
  {ab : Nat × Nat // ab ∈ finiteOrderedLeafPairs W} →
    Fin ((W.sup (fun w : Nat => w)) + 1)

/-- All new-new S2 numeric meet levels stabilize on the SAME
cofinal E5, mixed singleton, root S1/E2, old-old/new S2/E3
witnesses already produced by the preceding theorem.

The target S2 axiom supplies the exact cap, marker-1, or genuine
two-split classification for every new-new coordinate. -/
theorem RoleDiary.exists_cofinal_generic_joint_complete_S2_numeric_profile
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (W : Finset Nat) (hRoots : ∀ w : Nat, w ∈ W → IsLeaf K w)
    (B : Nat) (chi : Nat → Nat → Bool) :
    ∃ c : Fin B → Fin B → Bool,
      ∃ p : FiniteRootMeetProfile W,
        ∃ q : FiniteRootCrossPairMeetProfile W,
          ∃ r : FiniteRootNewNewPairMeetProfile W,
            (∀ w : {w : Nat // w ∈ W},
              IsOneSplit K (p w).val ∧ (p w).val < w.val) ∧
            (∀ ab : {ab : Nat × Nat // ab ∈ finiteOrderedLeafPairs W},
              ∀ w : {w : Nat // w ∈ W},
                (q ab w).val = min ab.val.1 w.val ∨
                (q ab w).val = 1 ∨ IsTwoSplit K (q ab w).val) ∧
            (∀ ab : {ab : Nat × Nat // ab ∈ finiteOrderedLeafPairs W},
              (r ab).val = min ab.val.1 ab.val.2 ∨
              (r ab).val = 1 ∨ IsTwoSplit K (r ab).val) ∧
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
                      ¬ K.edge (q ab w).val ab.val.1 ab.val.2))) ∧
              (∀ ab : {ab : Nat × Nat // ab ∈ finiteOrderedLeafPairs W},
                K.twoMeetLevel ab.val.1 (F t) ab.val.2 (F t) =
                  (r ab).val)) := by
  classical
  obtain ⟨c, p, q, hpRole, hqRole, hParent⟩ :=
    DK.exists_cofinal_generic_joint_E5_S1_E2_S2_E3
      G F hFLeaf W hRoots B chi
  let T := W.sup (fun w : Nat => w)
  let newNewProfile : Nat → FiniteRootNewNewPairMeetProfile W :=
    fun t ab =>
      ⟨K.twoMeetLevel ab.val.1 (F t) ab.val.2 (F t), by
        have hCap :
            K.twoMeetLevel ab.val.1 (F t) ab.val.2 (F t) ≤
              ab.val.1 :=
          (K.twoMeetLevel_le_min
            ab.val.1 (F t) ab.val.2 (F t)).trans
            (min_le_left _ _)
        have hMem :
            ab.val.1 ∈ W :=
          (Finset.mem_product.mp
            (Finset.mem_filter.mp ab.property).1).1
        have hBelow : ab.val.1 ≤ T :=
          Finset.le_sup (f := fun w : Nat => w) hMem
        omega⟩
  let R : FiniteRootNewNewPairMeetProfile W → Nat → Prop :=
    fun r N => ∃ t : Nat,
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
      (∀ ab : {ab : Nat × Nat // ab ∈ finiteOrderedLeafPairs W},
        ∀ w : {w : Nat // w ∈ W},
          K.twoMeetLevel ab.val.1 ab.val.2 w.val (F t) =
            (q ab w).val ∧
          (IsTwoSplit K (q ab w).val →
            (K.edge (q ab w).val w.val (F t) ↔
              ¬ K.edge (q ab w).val ab.val.1 ab.val.2))) ∧
      newNewProfile t = r
  have hDown : ∀ r : FiniteRootNewNewPairMeetProfile W,
      ∀ N M : Nat, M ≤ N → R r N → R r M := by
    intro r N M hMN
    rintro ⟨t, htN, hNumN, hT, hB, hLeaf, hColour,
      hPattern, hRootsT, hCrossT, hr⟩
    exact ⟨t, hMN.trans htN,
      lt_of_le_of_lt hMN hNumN,
      hT, hB, hLeaf, hColour, hPattern, hRootsT, hCrossT, hr⟩
  have hCover : ∀ N : Nat,
      ∃ r : FiniteRootNewNewPairMeetProfile W,
        r ∈ (Finset.univ : Finset (FiniteRootNewNewPairMeetProfile W)) ∧
        R r N := by
    intro N
    obtain ⟨t, htN, hNum, hB, htLeaf, hColour,
      hPattern, hRootsT, hCrossT⟩ := hParent N (max N T)
    have hNumN : N < F t :=
      lt_of_le_of_lt (le_max_left N T) hNum
    have hNumT : T < F t :=
      lt_of_le_of_lt (le_max_right N T) hNum
    exact ⟨newNewProfile t, Finset.mem_univ _, t, htN,
      hNumN, hNumT, hB, htLeaf, hColour,
      hPattern, hRootsT, hCrossT, rfl⟩
  obtain ⟨r, _hr, hAll⟩ :=
    finite_choice_persistent_of_downward_type
      (Finset.univ : Finset (FiniteRootNewNewPairMeetProfile W))
      R hDown hCover
  have hrRole
      (ab : {ab : Nat × Nat // ab ∈ finiteOrderedLeafPairs W}) :
      (r ab).val = min ab.val.1 ab.val.2 ∨
      (r ab).val = 1 ∨ IsTwoSplit K (r ab).val := by
    obtain ⟨t, _htN, _htNum, hT, _hB, htLeaf,
      _htColour, _htPattern, _htRoots, _htCross, hrT⟩ :=
        hAll (T + 1)
    have hAB : ab.val.1 < ab.val.2 :=
      (Finset.mem_filter.mp ab.property).2
    have hPairMem :
        (ab.val.1, ab.val.2) ∈ W.product W :=
      (Finset.mem_filter.mp ab.property).1
    obtain ⟨haMem, hbMem⟩ := Finset.mem_product.mp hPairMem
    have hA : IsLeaf K ab.val.1 := hRoots ab.val.1 haMem
    have hBLeaf : IsLeaf K ab.val.2 := hRoots ab.val.2 hbMem
    have hAVal : ab.val.1 ≤ T :=
      Finset.le_sup (f := fun w : Nat => w) haMem
    have hBVal : ab.val.2 ≤ T :=
      Finset.le_sup (f := fun w : Nat => w) hbMem
    have hAT : ab.val.1 < F t := by omega
    have hBT : ab.val.2 < F t := by omega
    have hMeet :
        K.twoMeetLevel ab.val.1 (F t) ab.val.2 (F t) =
          (r ab).val := by
      have h := congrArg
        (fun z : FiniteRootNewNewPairMeetProfile W => (z ab).val) hrT
      change K.twoMeetLevel ab.val.1 (F t) ab.val.2 (F t) =
        (r ab).val at h
      exact h
    have hCases := DK.pair_meets
      ab.val.1 (F t) ab.val.2 (F t)
      hAT hBT hA htLeaf hBLeaf htLeaf
    rw [hMeet] at hCases
    exact hCases
  refine ⟨c, p, q, r, hpRole, hqRole, hrRole, ?_⟩
  intro N M
  obtain ⟨t, ht, hImage, _hT, hB, htLeaf, htColour,
    htPattern, htRoots, htCross, hrT⟩ := hAll (max N M)
  refine ⟨t, (le_max_left _ _).trans ht,
    lt_of_le_of_lt (le_max_right _ _) hImage,
    hB, htLeaf, htColour, htPattern, htRoots, htCross, ?_⟩
  intro ab
  have h := congrArg
    (fun z : FiniteRootNewNewPairMeetProfile W => (z ab).val) hrT
  change K.twoMeetLevel ab.val.1 (F t) ab.val.2 (F t) =
    (r ab).val at h
  exact h

/-- Whenever a fixed new-new S2 coordinate is an actual target
two-split, its two new leaf pairs (a,v) and (b,v) have opposite
E3 incidence bits at that split. This V2 consequence is imposed
ONLY on genuine two-split coordinates, not capped or marker ones. -/
theorem RoleDiary.exists_cofinal_generic_joint_complete_S2_E3_profile
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (W : Finset Nat) (hRoots : ∀ w : Nat, w ∈ W → IsLeaf K w)
    (B : Nat) (chi : Nat → Nat → Bool) :
    ∃ c : Fin B → Fin B → Bool,
      ∃ p : FiniteRootMeetProfile W,
        ∃ q : FiniteRootCrossPairMeetProfile W,
          ∃ r : FiniteRootNewNewPairMeetProfile W,
            (∀ w : {w : Nat // w ∈ W},
              IsOneSplit K (p w).val ∧ (p w).val < w.val) ∧
            (∀ ab : {ab : Nat × Nat // ab ∈ finiteOrderedLeafPairs W},
              ∀ w : {w : Nat // w ∈ W},
                (q ab w).val = min ab.val.1 w.val ∨
                (q ab w).val = 1 ∨ IsTwoSplit K (q ab w).val) ∧
            (∀ ab : {ab : Nat × Nat // ab ∈ finiteOrderedLeafPairs W},
              (r ab).val = min ab.val.1 ab.val.2 ∨
              (r ab).val = 1 ∨ IsTwoSplit K (r ab).val) ∧
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
                      ¬ K.edge (q ab w).val ab.val.1 ab.val.2))) ∧
              (∀ ab : {ab : Nat × Nat // ab ∈ finiteOrderedLeafPairs W},
                K.twoMeetLevel ab.val.1 (F t) ab.val.2 (F t) =
                  (r ab).val ∧
                (IsTwoSplit K (r ab).val →
                  (K.edge (r ab).val ab.val.1 (F t) ↔
                    ¬ K.edge (r ab).val ab.val.2 (F t))))) := by
  classical
  obtain ⟨c, p, q, r, hpRole, hqRole, hrRole, hParent⟩ :=
    DK.exists_cofinal_generic_joint_complete_S2_numeric_profile
      G F hFLeaf W hRoots B chi
  refine ⟨c, p, q, r, hpRole, hqRole, hrRole, ?_⟩
  intro N M
  let T := W.sup (fun w : Nat => w)
  obtain ⟨t, htN, hNum, hB, htLeaf,
    htColour, htPattern, htRoots, htCross, htNewNew⟩ :=
      hParent N (max M T)
  have hM : M < F t :=
    lt_of_le_of_lt (le_max_left M T) hNum
  refine ⟨t, htN, hM, hB, htLeaf,
    htColour, htPattern, htRoots, htCross, ?_⟩
  intro ab
  have hMeet := htNewNew ab
  refine ⟨hMeet, ?_⟩
  intro hSplit
  have hPairMem :
      (ab.val.1, ab.val.2) ∈ W.product W :=
    (Finset.mem_filter.mp ab.property).1
  obtain ⟨haMem, hbMem⟩ := Finset.mem_product.mp hPairMem
  have hA : IsLeaf K ab.val.1 := hRoots ab.val.1 haMem
  have hBLeaf : IsLeaf K ab.val.2 := hRoots ab.val.2 hbMem
  have hCapA : (r ab).val ≤ ab.val.1 := by
    have hCap :=
      (K.twoMeetLevel_le_min
        ab.val.1 (F t) ab.val.2 (F t)).trans
        (min_le_left _ _)
    rw [hMeet] at hCap
    exact hCap
  have hCapB : (r ab).val ≤ ab.val.2 := by
    have hCap :=
      (K.twoMeetLevel_le_min
        ab.val.1 (F t) ab.val.2 (F t)).trans
        (min_le_right _ _)
    rw [hMeet] at hCap
    exact hCap
  have hNeA : (r ab).val ≠ ab.val.1 := by
    intro he
    have hBad : IsTwoSplit K ab.val.1 := by
      simpa only [he] using hSplit
    exact hA.2.2 hBad.2.2
  have hNeB : (r ab).val ≠ ab.val.2 := by
    intro he
    have hBad : IsTwoSplit K ab.val.2 := by
      simpa only [he] using hSplit
    exact hBLeaf.2.2 hBad.2.2
  have hBelowA : (r ab).val < ab.val.1 := by omega
  have hBelowB : (r ab).val < ab.val.2 := by omega
  have hOpp :
      ¬ (K.edge (r ab).val ab.val.1 (F t) ↔
          K.edge (r ab).val ab.val.2 (F t)) :=
    DK.twoSplit_witness_opposite_incidence
      (r ab).val ab.val.1 (F t) ab.val.2 (F t)
      hSplit hBelowA hBelowB hMeet
  tauto

end DiaryLeafPriority
end ThreeUniformDiaries
