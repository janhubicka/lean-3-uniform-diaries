import ThreeUniformDiaries.DiaryUniformGenericFullColourS1S2
import ThreeUniformDiaries.DiaryOneOldCutColourAllNewMeets
import ThreeUniformDiaries.DiaryCofinalGenericNewNewS2E3Profile
import ThreeUniformDiaries.DiaryGenericOldE5TargetLeafRange

/-!
# Track C: complete one-new-leaf S1/S2 generic profiles from ONE old-cut colour

English-first proof and adversarial audit:
  janhubicka/3-uniform-diaries PRs #311 and #312

The already CI-verified homogeneous generic full mixed-colour reservoir
fixes one B-singleton colour c, every numerical S1 meet with old roots,
and old-old/new full S2 meet profiles on entire induced generic copies.

When B lies STRICTLY above all old roots W, the numerical
new-new S2 meet twoMeet(a,v,b,v) of a fixed ordered old root pair
a<b is ALREADY DETERMINED by c, by exact tail full-pair meet
invariance. Choose one ACTUAL target leaf v0 in the high generic
c-fibre and record its finite new-new S2 profile r.
Every subsequent generic leaf in that same c-fibre has exactly r;
no second finite-colour choice is needed.

Full target RoleDiary ensures all p roles are true one-splits
and q/r satisfy capped-leaf, marker-one, or genuine two-split
alternatives. The numerical complete profile is existentially
selected, NOT source-prescribed; no functional finite candidate,
reserved successor or countable unavoidability follows.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- One finite old-cut complete mixed singleton colour already fixes
the WHOLE one-new-leaf numerical S1/S2 generator profile on
arbitrarily high induced generic subcopies, including the
previously missing new-new S2 pair family.

The finite target Cut must be strictly above all numerical old
root values. Both the anchor and every leaf of each later
generic subcopy are chosen ABOVE Cut; exact old-cut colour
equality then forces every new-new S2 meet literally.

The resulting c,p,q,r are fixed before the tail bound M, and
every generic subcopy is an actual AuxTypeRespecting induced copy
in the original prescribed unordered true-leaf range. The
profiles need not be the SOURCE-required generator values. -/
theorem RoleDiary.exists_uniform_generic_complete_oneNew_S1_S2_profiles
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (W : Finset Nat) (hRoots : ∀ w : Nat, w ∈ W → IsLeaf K w)
    (Cut : Nat)
    (hCut : (W.sup (fun w : Nat => w)) < Cut) :
    ∃ c : Fin Cut → Fin Cut → Bool,
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
            (∀ M : Nat,
              ∃ (u : Ordered3Graph.Embedding G.graph G.graph),
                u.AuxTypeRespecting ∧
                ∀ t : Nat,
                  M < F (u t) ∧ IsLeaf K (F (u t)) ∧
                  DiaryLowerBoundColors.singletonColour K Cut (F (u t)) = c ∧
                  (∀ w : {w : Nat // w ∈ W},
                    K.oneMeetLevel w.val (F (u t)) = (p w).val) ∧
                  (∀ ab : {ab : Nat × Nat //
                      ab ∈ finiteOrderedLeafPairs W},
                    ∀ w : {w : Nat // w ∈ W},
                      K.twoMeetLevel ab.val.1 ab.val.2
                        w.val (F (u t)) = (q ab w).val) ∧
                  (∀ ab : {ab : Nat × Nat // ab ∈ finiteOrderedLeafPairs W},
                    K.twoMeetLevel ab.val.1 (F (u t))
                      ab.val.2 (F (u t)) = (r ab).val)) := by
  classical
  let T : Nat := W.sup (fun w : Nat => w)
  obtain ⟨c, p, q, hOneRole, hCrossRole, hAll⟩ :=
    DK.exists_uniform_generic_fullColour_S1_S2_subcopies
      G F hFLeaf W hRoots Cut
  obtain ⟨u0, _hu0, hAll0⟩ := hAll Cut
  let v0 : Nat := F (u0 0)
  obtain ⟨hv0High, hv0Leaf, hv0Colour, _hv0One, _hv0Cross⟩ := hAll0 0
  have hv0After : Cut < v0 := hv0High
  let r : FiniteRootNewNewPairMeetProfile W := fun ab =>
    ⟨K.twoMeetLevel ab.val.1 v0 ab.val.2 v0, by
      have hCap : K.twoMeetLevel ab.val.1 v0 ab.val.2 v0 ≤
          ab.val.1 :=
        (K.twoMeetLevel_le_min
          ab.val.1 v0 ab.val.2 v0).trans (min_le_left _ _)
      have hOldPair :
          (ab.val.1, ab.val.2) ∈ W.product W :=
        (Finset.mem_filter.mp ab.property).1
      have hMem : ab.val.1 ∈ W :=
        (Finset.mem_product.mp hOldPair).1
      have hBound : ab.val.1 ≤ T :=
        Finset.le_sup (f := fun x : Nat => x) hMem
      omega⟩
  have hNewNewRole
      (ab : {ab : Nat × Nat // ab ∈ finiteOrderedLeafPairs W}) :
      (r ab).val = min ab.val.1 ab.val.2 ∨
      (r ab).val = 1 ∨ IsTwoSplit K (r ab).val := by
    have hOldPair :
        (ab.val.1, ab.val.2) ∈ W.product W :=
      (Finset.mem_filter.mp ab.property).1
    obtain ⟨haW, hbW⟩ := Finset.mem_product.mp hOldPair
    have hA : IsLeaf K ab.val.1 := hRoots ab.val.1 haW
    have hB : IsLeaf K ab.val.2 := hRoots ab.val.2 hbW
    have hABound : ab.val.1 ≤ T :=
      Finset.le_sup (f := fun x : Nat => x) haW
    have hBBound : ab.val.2 ≤ T :=
      Finset.le_sup (f := fun x : Nat => x) hbW
    have haV : ab.val.1 < v0 := by omega
    have hbV : ab.val.2 < v0 := by omega
    have hCases := DK.pair_meets
      ab.val.1 v0 ab.val.2 v0
      haV hbV hA hv0Leaf hB hv0Leaf
    change
      K.twoMeetLevel ab.val.1 v0 ab.val.2 v0 =
        min ab.val.1 ab.val.2 ∨
      K.twoMeetLevel ab.val.1 v0 ab.val.2 v0 = 1 ∨
        IsTwoSplit K (K.twoMeetLevel ab.val.1 v0 ab.val.2 v0)
    exact hCases
  refine ⟨c, p, q, r, hOneRole, hCrossRole, hNewNewRole, ?_⟩
  intro M
  obtain ⟨u, hu, hEvery⟩ := hAll (max M Cut)
  refine ⟨u, hu, ?_⟩
  intro n
  obtain ⟨hHigh, hLeaf, hColour, hOne, hCross⟩ := hEvery n
  have hCandidateCut : Cut < F (u n) :=
    lt_of_le_of_lt (le_max_right M Cut) hHigh
  have hSameColour :
      DiaryLowerBoundColors.singletonColour K Cut v0 =
        DiaryLowerBoundColors.singletonColour K Cut (F (u n)) :=
    hv0Colour.trans hColour.symm
  have hNewNew
      (ab : {ab : Nat × Nat // ab ∈ finiteOrderedLeafPairs W}) :
      K.twoMeetLevel ab.val.1 (F (u n)) ab.val.2 (F (u n)) =
        (r ab).val := by
    have hOldPair :
        (ab.val.1, ab.val.2) ∈ W.product W :=
      (Finset.mem_filter.mp ab.property).1
    obtain ⟨haW, hbW⟩ := Finset.mem_product.mp hOldPair
    have hABound : ab.val.1 ≤ T :=
      Finset.le_sup (f := fun x : Nat => x) haW
    have hBBound : ab.val.2 ≤ T :=
      Finset.le_sup (f := fun x : Nat => x) hbW
    have haCut : ab.val.1 < Cut := by omega
    have hbCut : ab.val.2 < Cut := by omega
    have haV0 : ab.val.1 < v0 := lt_trans haCut hv0After
    have haV : ab.val.1 < F (u n) :=
      lt_trans haCut hCandidateCut
    have hEq := same_complete_singletonColour_fixes_all_oneNew_meets
      K Cut ab.val.1 ab.val.2 ab.val.2
      v0 (F (u n)) haCut hbCut haV0 haV hSameColour
    change
      K.twoMeetLevel ab.val.1 (F (u n)) ab.val.2 (F (u n)) =
        K.twoMeetLevel ab.val.1 v0 ab.val.2 v0
    exact hEq.2.2.symm
  refine ⟨lt_of_le_of_lt (le_max_left M Cut) hHigh,
    hLeaf, hColour, hOne, hCross, hNewNew⟩

/-- The same COMPLETE one-new-leaf numerical S1/S2 profile is
available on induced generic subcopies inside ANY finite old
E5-pattern fibre of the ORIGINAL prescribed unordered true-leaf
range. The numeric profile is selected existentially from the
target and not asserted source-compatible. -/
theorem RoleDiary.exists_uniform_generic_oldE5_complete_oneNew_S1_S2_reservoir
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (A : Finset Nat) (theta : Nat → Nat → Bool)
    (W : Finset Nat) (hRoots : ∀ w : Nat, w ∈ W → IsLeaf K w)
    (Cut M : Nat)
    (hCut : (W.sup (fun w : Nat => w)) < Cut) :
    ∃ J : Ordered3Graph.UnorderedEmbedding G.graph K,
      (∀ n : Nat, M < J n ∧ IsLeaf K (J n) ∧
        ∃ t : Nat, J n = F t) ∧
      (∀ n a : Nat, a ∈ A → F a < J n) ∧
      (∀ n a b : Nat, a ∈ A → b ∈ A → a < b →
        (K.unorderedEdge (F a) (F b) (J n) ↔ theta a b = true)) ∧
      ∃ c : Fin Cut → Fin Cut → Bool,
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
              (∀ B : Nat,
                ∃ (u : Ordered3Graph.Embedding G.graph G.graph),
                  u.AuxTypeRespecting ∧
                  ∀ t : Nat,
                    B < J (u t) ∧ IsLeaf K (J (u t)) ∧
                    DiaryLowerBoundColors.singletonColour K Cut (J (u t)) = c ∧
                    (∀ w : {w : Nat // w ∈ W},
                      K.oneMeetLevel w.val (J (u t)) = (p w).val) ∧
                    (∀ ab : {ab : Nat × Nat //
                        ab ∈ finiteOrderedLeafPairs W},
                      ∀ w : {w : Nat // w ∈ W},
                        K.twoMeetLevel ab.val.1 ab.val.2
                          w.val (J (u t)) = (q ab w).val) ∧
                    (∀ ab : {ab : Nat × Nat // ab ∈ finiteOrderedLeafPairs W},
                      K.twoMeetLevel ab.val.1 (J (u t))
                        ab.val.2 (J (u t)) = (r ab).val)) := by
  obtain ⟨J, hRange, hAboveOld, hPattern⟩ :=
    exists_generic_leaf_subcopy_in_prescribed_oldE5_fibre
      G K F hFLeaf A theta M
  have hJLeaf : ∀ t : Nat, IsLeaf K (J t) := by
    intro t
    exact (hRange t).2.1
  obtain ⟨c, p, q, r, hOneRole, hCrossRole, hNewNewRole, hAll⟩ :=
    DK.exists_uniform_generic_complete_oneNew_S1_S2_profiles
      G J hJLeaf W hRoots Cut hCut
  exact ⟨J, hRange, hAboveOld, hPattern,
    c, p, q, r, hOneRole, hCrossRole, hNewNewRole, hAll⟩

end DiaryLeafPriority
end ThreeUniformDiaries
