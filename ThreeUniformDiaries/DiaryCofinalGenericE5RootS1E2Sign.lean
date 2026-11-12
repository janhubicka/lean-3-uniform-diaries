import ThreeUniformDiaries.DiaryCofinalGenericE5RootS1JointProfile
import ThreeUniformDiaries.DiaryHighTwoSidedE2RangeWitness

/-!
# Track A: a stabilized root S1 profile fixes all corresponding E2 right bits

The new genuine joint cofinal geometry from Track A combines one
arbitrary finite leaf-only E5 pattern, one complete mixed singleton
colour at a prescribed finite cut, and ONE exact finite numerical S1
meet vector against a family of old target leaf roots W.

The full target RoleDiary V1 axiom forces the E2 bits at every such
one-split: when old root w lies before new genuine leaf v and the
S1 meet is s, the two target leaves w and v are on opposite E2
branches at s. Therefore the whole E2 bit vector of all new leaves
in this cofinal joint fibre is not an extra arbitrary choice; it
is exactly the complement of the already fixed old-root bits.

These are ACTUAL E2 incidences, not merely formal split profiles.
Their values are still existential, determined by the chosen profile
p and fixed roots; they need not agree with a source-required E2
orientation, and no E3/S2/relative order/generator-functionality/
future-horizon persistence is asserted.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- In an original prescribed unordered generic true-leaf range,
the complete old-pair E5 pattern, full cut-B singleton colour,
exact numeric S1 meets with all roots, and right E2 branches at
those meets are ALL cofinally realized by THE SAME new leaves.

The S1 profile is chosen existentially and remains fixed before
both cofinal lower bounds. Each right E2 bit is literally the
negation of the corresponding old root's edge at that split. -/
theorem RoleDiary.exists_cofinal_generic_E5_pattern_and_finiteRoot_S1_E2
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (W : Finset Nat) (hRoots : ∀ w : Nat, w ∈ W → IsLeaf K w)
    (B : Nat) (chi : Nat → Nat → Bool) :
    ∃ c : Fin B → Fin B → Bool,
      ∃ p : FiniteRootMeetProfile W,
        (∀ w : {w : Nat // w ∈ W},
          IsOneSplit K (p w).val ∧ (p w).val < w.val) ∧
        (∀ N M : Nat, ∃ t : Nat,
          N ≤ t ∧ M < F t ∧ B < F t ∧ IsLeaf K (F t) ∧
          DiaryLowerBoundColors.singletonColour K B (F t) = c ∧
          (∀ i j : Nat, F i < F j → F j < B →
            (K.edge (F i) (F j) (F t) ↔
              chi (F i) (F j) = true)) ∧
          (∀ w : {w : Nat // w ∈ W},
            K.oneMeetLevel w.val (F t) = (p w).val ∧
            (K.edge 0 (p w).val (F t) ↔
              ¬ K.edge 0 (p w).val w.val))) := by
  classical
  obtain ⟨c, p, hRole, hAll⟩ :=
    DK.exists_cofinal_generic_E5_pattern_and_finiteRootMeetProfile
      G F hFLeaf W hRoots B chi
  refine ⟨c, p, hRole, ?_⟩
  intro N M
  let T := W.sup (fun w : Nat => w)
  obtain ⟨t, htN, hTarget, hB, htLeaf, hColour, hPair, hMeet⟩ :=
    hAll N (max M T)
  have hActualM : M < F t :=
    lt_of_le_of_lt (le_max_left M T) hTarget
  refine ⟨t, htN, hActualM, hB, htLeaf, hColour, hPair, ?_⟩
  intro w
  have hWBound : w.val ≤ T :=
    Finset.le_sup (f := fun x : Nat => x) w.property
  have hWLt : w.val < F t :=
    lt_of_le_of_lt hWBound
      (lt_of_le_of_lt (le_max_right M T) hTarget)
  have hSplit : IsOneSplit K (p w).val := (hRole w).1
  have hSW : (p w).val < w.val := (hRole w).2
  have hST : (p w).val < F t := lt_trans hSW hWLt
  have hOpp :
      ¬ (K.edge 0 (p w).val w.val ↔
          K.edge 0 (p w).val (F t)) :=
    DK.oneSplit_witness_opposite_marker
      (p w).val w.val (F t)
      hSplit (hRoots w.val w.property) htLeaf
      hSW hST (hMeet w)
  exact ⟨hMeet w, by tauto⟩

end DiaryLeafPriority
end ThreeUniformDiaries
