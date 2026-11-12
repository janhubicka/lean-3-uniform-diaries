import ThreeUniformDiaries.DiaryOldStageCofinalE5S1E2Profile
import ThreeUniformDiaries.DiaryCofinalGenericE5RootS1E2Sign
import ThreeUniformDiaries.DiaryCofinalGenericE5RootS1JointProfile
import ThreeUniformDiaries.DiaryStableGenericPairPatternColour
import ThreeUniformDiaries.DiaryExactSingletonColourSplitCut

/-!
# Track C: pattern-controlled infinite high S1 cone in a generic leaf range

English-first proof and adversarial scope audit:
  janhubicka/3-uniform-diaries PR #295

The cofinally recurrent full mixed singleton colour supplied by the
verified generic finite-pattern theorem can be realized on an infinite
sequence of ORIGINAL prescribed generic leaves, strictly increasing
in both SOURCE index and TARGET numerical position.

Every selected leaf has the same complete B-colour and realizes the
whole prescribed old generic leaf-pair edge/nonedge pattern below B.
By the full target RoleDiary exact S1 cutoff, EVERY pair of selected
leaves has a genuine one-split meet at least B.

This supplies no prescribed exact split/marker S1/S2/E2/E3 table,
generic subcopy inside the selected colour, or persistent successor.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- An infinite high one-split cone can be selected from the SAME
original unordered generic induced true-leaf range while EVERY
selected leaf realizes an arbitrarily prescribed Boolean edge/nonedge
pattern on all old generic-range leaf pairs below cut B.

The selected source indices and target image positions are BOTH
strictly increasing, even though the original map F need not be
numerically increasing. All pairwise meets are genuine S1 one-splits
at levels >= B, but their exact levels are not prescribed. -/
theorem RoleDiary.exists_infinite_high_oneSplit_cone_with_generic_pair_pattern
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hLeaves : ∀ t : Nat, IsLeaf K (F t))
    (B N M : Nat) (chi : Nat → Nat → Bool) :
    ∃ c : Fin B → Fin B → Bool,
      ∃ indices : Nat → Nat,
        StrictMono indices ∧
        StrictMono (fun k : Nat => F (indices k)) ∧
        (∀ k : Nat,
          N ≤ indices k ∧
          M < F (indices k) ∧
          B < F (indices k) ∧
          IsLeaf K (F (indices k)) ∧
          DiaryLowerBoundColors.singletonColour K B (F (indices k)) = c ∧
          (∀ i j : Nat, F i < F j → F j < B →
            (K.edge (F i) (F j) (F (indices k)) ↔
              chi (F i) (F j) = true))) ∧
        (∀ i j : Nat, i < j →
          IsOneSplit K
            (K.oneMeetLevel (F (indices i)) (F (indices j))) ∧
          B ≤ K.oneMeetLevel (F (indices i)) (F (indices j))) := by
  classical
  obtain ⟨c, hRec⟩ :=
    exists_cofinal_generic_pair_pattern_full_colour
      G K F hLeaves B chi
  let pick : Nat → Nat → Nat := fun n m =>
    Classical.choose (hRec n m)
  have hPick (n m : Nat) :
      n ≤ pick n m ∧
      m < F (pick n m) ∧
      B < F (pick n m) ∧
      IsLeaf K (F (pick n m)) ∧
      DiaryLowerBoundColors.singletonColour K B (F (pick n m)) = c ∧
      (∀ i j : Nat, F i < F j → F j < B →
        (K.edge (F i) (F j) (F (pick n m)) ↔
          chi (F i) (F j) = true)) :=
    Classical.choose_spec (hRec n m)
  let indices : Nat → Nat :=
    Nat.rec (pick N (max B M))
      (fun _ prev => pick (prev + 1) (max M (F prev)))
  have hSrcStep (k : Nat) : indices k < indices (k + 1) := by
    change indices k < pick (indices k + 1) (max M (F (indices k)))
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (hPick _ _).1
  have hTarStep (k : Nat) :
      F (indices k) < F (indices (k + 1)) := by
    change F (indices k) <
      F (pick (indices k + 1) (max M (F (indices k))))
    exact lt_of_le_of_lt
      (le_max_right M (F (indices k))) (hPick _ _).2.1
  have hSrcMono : StrictMono indices :=
    strictMono_nat_of_lt_succ hSrcStep
  have hTarMono : StrictMono (fun k : Nat => F (indices k)) :=
    strictMono_nat_of_lt_succ hTarStep
  have hIndex (k : Nat) : N ≤ indices k := by
    induction k with
    | zero =>
      change N ≤ pick N (max B M)
      exact (hPick _ _).1
    | succ k ih =>
      exact ih.trans (hSrcStep k).le
  have hInfo (k : Nat) :
      M < F (indices k) ∧
      B < F (indices k) ∧
      IsLeaf K (F (indices k)) ∧
      DiaryLowerBoundColors.singletonColour K B (F (indices k)) = c ∧
      (∀ i j : Nat, F i < F j → F j < B →
        (K.edge (F i) (F j) (F (indices k)) ↔
          chi (F i) (F j) = true)) := by
    cases k with
    | zero =>
      obtain ⟨_hN, hMax, _hB, hLeaf, hColour, hPattern⟩ :=
        hPick N (max B M)
      change M < F (pick N (max B M)) ∧
        B < F (pick N (max B M)) ∧
        IsLeaf K (F (pick N (max B M))) ∧
        DiaryLowerBoundColors.singletonColour K B (F (pick N (max B M))) = c ∧
        (∀ i j : Nat, F i < F j → F j < B →
          (K.edge (F i) (F j) (F (pick N (max B M))) ↔
            chi (F i) (F j) = true))
      exact ⟨lt_of_le_of_lt (le_max_right B M) hMax,
        lt_of_le_of_lt (le_max_left B M) hMax,
        hLeaf, hColour, hPattern⟩
    | succ k =>
      obtain ⟨_hN, hMax, hB, hLeaf, hColour, hPattern⟩ :=
        hPick (indices k + 1) (max M (F (indices k)))
      change M < F (pick (indices k + 1) (max M (F (indices k)))) ∧
        B < F (pick (indices k + 1) (max M (F (indices k)))) ∧
        IsLeaf K (F (pick (indices k + 1) (max M (F (indices k))))) ∧
        DiaryLowerBoundColors.singletonColour K B
          (F (pick (indices k + 1) (max M (F (indices k))))) = c ∧
        (∀ i j : Nat, F i < F j → F j < B →
          (K.edge (F i) (F j)
              (F (pick (indices k + 1) (max M (F (indices k))))) ↔
            chi (F i) (F j) = true))
      exact ⟨lt_of_le_of_lt (le_max_left M (F (indices k))) hMax,
        hB, hLeaf, hColour, hPattern⟩
  refine ⟨c, indices, hSrcMono, hTarMono, ?_, ?_⟩
  · intro k
    obtain ⟨hM, hB, hLeaf, hColour, hPattern⟩ := hInfo k
    exact ⟨hIndex k, hM, hB, hLeaf, hColour, hPattern⟩
  · intro i j hij
    obtain ⟨_hMi, _hBi, hLeafI, hColourI, _hPatternI⟩ := hInfo i
    obtain ⟨_hMj, _hBj, hLeafJ, hColourJ, _hPatternJ⟩ := hInfo j
    have hNe : F (indices i) ≠ F (indices j) :=
      ne_of_lt (hTarMono hij)
    have hOne : IsOneSplit K
        (K.oneMeetLevel (F (indices i)) (F (indices j))) :=
      DK.singleton_meets _ _ hLeafI hLeafJ hNe
    have hEqColour :
        DiaryLowerBoundColors.singletonColour K B (F (indices i)) =
          DiaryLowerBoundColors.singletonColour K B (F (indices j)) :=
      hColourI.trans hColourJ.symm
    have hMeet : B ≤ K.oneMeetLevel (F (indices i)) (F (indices j)) :=
      (DK.singletonColour_eq_iff_cut_le_oneMeet
        hLeafI hLeafJ hNe B).mp hEqColour
    exact ⟨hOne, hMeet⟩

end DiaryLeafPriority
end ThreeUniformDiaries
