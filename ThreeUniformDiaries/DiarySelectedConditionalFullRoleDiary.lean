import ThreeUniformDiaries.DiarySelectedColimitSplitWitnesses

/-!
# Track B: the selected finite absorber tower has a full countable diary limit,
# CONDITIONAL on the still-unproved bounded-forward-rank invariant

The two EXISTENTIAL V1/V2 witness clauses are already handled by
transporting ONE actual finite-stage witness through the coherent
selected stable-rank embedding. Every remaining V/E/S condition is
local in finitely many vertices, edges and exact capped numerical
meets. The verified eventual literal-prefix theorem supplies ONE
genuine finite full diary stage for each such finite test, not a
fictitious RoleDiary structure on the unused Nat tail.

Nothing in this file proves that the ACTUAL Classical.choice-selected
absorber tower has bounded ranks; that construction problem remains
OPEN. This is also not countable-source every-target-flip absorption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Every finite numerical cut in the conditional countable edge
limit is literally the same full raw edge/nonedge table as the
initial segment of ONE sufficiently late genuine finite full diary.
That finite target also contains the entire chosen cut. -/
theorem selectedAbsorberLimit_exists_full_finite_prefix
    (hb : selectedAbsorberFiniteOrderTower.BoundedRanks)
    (r : Nat) :
    ∃ n : Nat, r ≤ (universalStrongAbsorberTower n).bound ∧
      LiteralOldPrefixAgreement
        (selectedAbsorberFiniteEdgeTower.limitGraph
          (selectedAbsorberFiniteEdgeTower_prefix_of_boundedRanks hb))
        (universalStrongAbsorberTower n).graph r := by
  let hp := selectedAbsorberFiniteEdgeTower_prefix_of_boundedRanks hb
  let n := edgePrefixCutoff hp r
  have hSpec := edgePrefixCutoff_spec hp r n (le_refl _)
  refine ⟨n, ?_, ?_⟩
  · exact hSpec.1
  · exact selectedAbsorberLimit_literalOldPrefix hb r n (le_refl _)

/-- The manuscript's LexEarlier comparison is FINITARY: literal
prefix agreement on a,b also transfers their exact singleton
meet, the corresponding full pair meet and the final deciding
edge. The bound is on the two leaf coordinates, NOT on all type
cuts, since type tests have old last coordinates. -/
theorem lexEarlier_iff_of_literalOldPrefix
    {A B : Ordered3Graph Nat} {r : Nat}
    (h : LiteralOldPrefixAgreement A B r)
    (a b : Nat) (ha : a < r) (hb : b < r) :
    LexEarlier A a b ↔ LexEarlier B a b := by
  have hOne :=
    oneMeetLevel_eq_of_literalOldPrefix h a b ha hb
  have hm : B.oneMeetLevel a b < r := by
    have hcap := B.oneMeetLevel_le_min a b
    omega
  have hTwo :=
    twoMeetLevel_eq_of_literalOldPrefix h
      (B.oneMeetLevel a b) a (B.oneMeetLevel a b) b
      hm ha hm hb
  have hBit :=
    h (B.twoMeetLevel (B.oneMeetLevel a b) a (B.oneMeetLevel a b) b)
      (B.oneMeetLevel a b) b hb
  simp only [LexEarlier, hOne, hTwo, hBit]

/-- Full role coverage passes to the countable limit from an
actual bounded finite frame covering each individual vertex. -/
theorem selectedAbsorberLimit_role_valid
    (hb : selectedAbsorberFiniteOrderTower.BoundedRanks) :
    let K := selectedAbsorberFiniteEdgeTower.limitGraph
      (selectedAbsorberFiniteEdgeTower_prefix_of_boundedRanks hb)
    ∀ v : Nat, 3 ≤ v →
      IsLeaf K v ∨ IsOneSplit K v ∨ IsTwoSplit K v := by
  dsimp only
  intro v hv
  obtain ⟨n,hFrame,hPrefix⟩ :=
    selectedAbsorberLimit_exists_full_finite_prefix hb (v+1)
  have hvn : v < (universalStrongAbsorberTower n).bound := by omega
  have hRole := role_iff_of_literalOldPrefix hPrefix v (by omega)
  rcases (universalStrongAbsorberTower n).diary.prediary.role_valid
      v hv hvn with hLeaf | hOne | hTwo
  · exact Or.inl (hRole.1.mpr hLeaf)
  · exact Or.inr (Or.inl (hRole.2.1.mpr hOne))
  · exact Or.inr (Or.inr (hRole.2.2.mpr hTwo))

/-- V1 universal coherence transfers by one literal finite prefix:
all roles, both positive incidences and the complete singleton
type comparison are old-prefix data. -/
theorem selectedAbsorberLimit_oneSplit_coherent
    (hb : selectedAbsorberFiniteOrderTower.BoundedRanks) :
    let K := selectedAbsorberFiniteEdgeTower.limitGraph
      (selectedAbsorberFiniteEdgeTower_prefix_of_boundedRanks hb)
    ∀ s a b : Nat, IsOneSplit K s → IsLeaf K a → IsLeaf K b →
      K.edge 0 s a → K.edge 0 s b →
      K.SameOneTypeBelow s a b := by
  dsimp only
  intro s a b hs ha hbLeaf heA heB
  let r := max s (max a b) + 1
  obtain ⟨n,hFrame,hPrefix⟩ :=
    selectedAbsorberLimit_exists_full_finite_prefix hb r
  have hsR : s < r := by dsimp [r]; omega
  have haR : a < r := by dsimp [r]; omega
  have hbR : b < r := by dsimp [r]; omega
  have hsFinite : IsOneSplit (universalStrongAbsorberTower n).graph s :=
    (role_iff_of_literalOldPrefix hPrefix s hsR).2.1.mp hs
  have haFinite : IsLeaf (universalStrongAbsorberTower n).graph a :=
    (role_iff_of_literalOldPrefix hPrefix a haR).1.mp ha
  have hbFinite : IsLeaf (universalStrongAbsorberTower n).graph b :=
    (role_iff_of_literalOldPrefix hPrefix b hbR).1.mp hbLeaf
  have hEaFinite : (universalStrongAbsorberTower n).graph.edge 0 s a :=
    (hPrefix 0 s a haR).mp heA
  have hEbFinite : (universalStrongAbsorberTower n).graph.edge 0 s b :=
    (hPrefix 0 s b hbR).mp heB
  have hType :=
    (universalStrongAbsorberTower n).diary.prediary.one_split_coherent
      s a b hsFinite haFinite hbFinite hEaFinite hEbFinite
  exact (sameOneTypeBelow_iff_of_literalOldPrefix
      hPrefix a b s haR hbR).mpr hType

/-- V2 universal coherence transfers on one finite cut containing
the split and every coordinate of both ordered leaf pairs. -/
theorem selectedAbsorberLimit_twoSplit_coherent
    (hb : selectedAbsorberFiniteOrderTower.BoundedRanks) :
    let K := selectedAbsorberFiniteEdgeTower.limitGraph
      (selectedAbsorberFiniteEdgeTower_prefix_of_boundedRanks hb)
    ∀ s a b c d : Nat, IsTwoSplit K s → a < b → c < d →
      IsLeaf K a → IsLeaf K b → IsLeaf K c → IsLeaf K d →
      K.edge s a b → K.edge s c d →
      K.SameTwoTypeBelow s a b c d := by
  dsimp only
  intro s a b c d hs hab hcd ha hbLeaf hc hd heAB heCD
  let r := max s (max (max a b) (max c d)) + 1
  obtain ⟨n,hFrame,hPrefix⟩ :=
    selectedAbsorberLimit_exists_full_finite_prefix hb r
  have hsR : s < r := by dsimp [r]; omega
  have haR : a < r := by dsimp [r]; omega
  have hbR : b < r := by dsimp [r]; omega
  have hcR : c < r := by dsimp [r]; omega
  have hdR : d < r := by dsimp [r]; omega
  have hsFinite : IsTwoSplit (universalStrongAbsorberTower n).graph s :=
    (role_iff_of_literalOldPrefix hPrefix s hsR).2.2.mp hs
  have haFinite : IsLeaf (universalStrongAbsorberTower n).graph a :=
    (role_iff_of_literalOldPrefix hPrefix a haR).1.mp ha
  have hbFinite : IsLeaf (universalStrongAbsorberTower n).graph b :=
    (role_iff_of_literalOldPrefix hPrefix b hbR).1.mp hbLeaf
  have hcFinite : IsLeaf (universalStrongAbsorberTower n).graph c :=
    (role_iff_of_literalOldPrefix hPrefix c hcR).1.mp hc
  have hdFinite : IsLeaf (universalStrongAbsorberTower n).graph d :=
    (role_iff_of_literalOldPrefix hPrefix d hdR).1.mp hd
  have heABFinite : (universalStrongAbsorberTower n).graph.edge s a b :=
    (hPrefix s a b hbR).mp heAB
  have heCDFinite : (universalStrongAbsorberTower n).graph.edge s c d :=
    (hPrefix s c d hdR).mp heCD
  have hType :=
    (universalStrongAbsorberTower n).diary.prediary.two_split_coherent
      s a b c d hsFinite hab hcd
      haFinite hbFinite hcFinite hdFinite heABFinite heCDFinite
  exact (sameTwoTypeBelow_iff_of_literalOldPrefix
      hPrefix a b c d s haR hbR hcR hdR).mpr hType

/-- Both V3 leaf-marker equivalences pass to the countable limit;
their LexEarlier predicates are preserved by the same literal
prefix, including the final full-pair-meet deciding edge. -/
theorem selectedAbsorberLimit_leaf_markers
    (hb : selectedAbsorberFiniteOrderTower.BoundedRanks) :
    let K := selectedAbsorberFiniteEdgeTower.limitGraph
      (selectedAbsorberFiniteEdgeTower_prefix_of_boundedRanks hb)
    (∀ a b : Nat, a < b → IsLeaf K a → IsLeaf K b →
      (K.edge 1 a b ↔ LexEarlier K a b)) ∧
    (∀ a b : Nat, a < b → IsLeaf K a → IsLeaf K b →
      (K.edge 2 a b ↔ ¬ LexEarlier K a b)) := by
  dsimp only
  constructor
  · intro a b hab ha hbLeaf
    obtain ⟨n,hFrame,hPrefix⟩ :=
      selectedAbsorberLimit_exists_full_finite_prefix hb (b+1)
    have haR : a < b+1 := by omega
    have hbR : b < b+1 := by omega
    have hbn : b < (universalStrongAbsorberTower n).bound := by omega
    have haFinite : IsLeaf (universalStrongAbsorberTower n).graph a :=
      (role_iff_of_literalOldPrefix hPrefix a haR).1.mp ha
    have hbFinite : IsLeaf (universalStrongAbsorberTower n).graph b :=
      (role_iff_of_literalOldPrefix hPrefix b hbR).1.mp hbLeaf
    have hLex := lexEarlier_iff_of_literalOldPrefix
      hPrefix a b haR hbR
    exact (hPrefix 1 a b hbR).trans
      (((universalStrongAbsorberTower n).diary.prediary.leaf_marker_one
        a b hab hbn haFinite hbFinite).trans hLex.symm)
  · intro a b hab ha hbLeaf
    obtain ⟨n,hFrame,hPrefix⟩ :=
      selectedAbsorberLimit_exists_full_finite_prefix hb (b+1)
    have haR : a < b+1 := by omega
    have hbR : b < b+1 := by omega
    have hbn : b < (universalStrongAbsorberTower n).bound := by omega
    have haFinite : IsLeaf (universalStrongAbsorberTower n).graph a :=
      (role_iff_of_literalOldPrefix hPrefix a haR).1.mp ha
    have hbFinite : IsLeaf (universalStrongAbsorberTower n).graph b :=
      (role_iff_of_literalOldPrefix hPrefix b hbR).1.mp hbLeaf
    have hLex := lexEarlier_iff_of_literalOldPrefix
      hPrefix a b haR hbR
    exact (hPrefix 2 a b hbR).trans
      (((universalStrongAbsorberTower n).diary.prediary.leaf_marker_two
        a b hab hbn haFinite hbFinite).trans (not_congr hLex.symm))

/-- The permitted-edge E1–E5 classification is local in the
increasing triple and the marker roles of its three vertices. -/
theorem selectedAbsorberLimit_permitted_edge
    (hb : selectedAbsorberFiniteOrderTower.BoundedRanks) :
    let K := selectedAbsorberFiniteEdgeTower.limitGraph
      (selectedAbsorberFiniteEdgeTower_prefix_of_boundedRanks hb)
    ∀ x y z : Nat, K.edge x y z → PermittedDiaryEdge K x y z := by
  dsimp only
  intro x y z he
  have hOrder :=
    selectedAbsorberFiniteEdgeTower.limitGraph_edge_ordered
      (selectedAbsorberFiniteEdgeTower_prefix_of_boundedRanks hb)
      x y z he
  obtain ⟨n,hFrame,hPrefix⟩ :=
    selectedAbsorberLimit_exists_full_finite_prefix hb (z+1)
  have hxR : x < z+1 := by omega
  have hyR : y < z+1 := by omega
  have hzR : z < z+1 := by omega
  have heFinite : (universalStrongAbsorberTower n).graph.edge x y z :=
    (hPrefix x y z hzR).mp he
  have hPerm :=
    (universalStrongAbsorberTower n).diary.prediary.permitted_edge
      x y z heFinite
  have hX := role_iff_of_literalOldPrefix hPrefix x hxR
  have hY := role_iff_of_literalOldPrefix hPrefix y hyR
  have hZ := role_iff_of_literalOldPrefix hPrefix z hzR
  simpa only [PermittedDiaryEdge,
    hX.1,hX.2.1,hX.2.2,
    hY.1,hY.2.1,hY.2.2,
    hZ.1,hZ.2.1,hZ.2.2] using hPerm

/-- Full S1 for any two DISTINCT countable limit leaves.
The finite source axiom is applied only inside its ACTUAL bound,
and its numerical one-meet is preserved by the old-prefix theorem. -/
theorem selectedAbsorberLimit_singleton_meets
    (hb : selectedAbsorberFiniteOrderTower.BoundedRanks) :
    let K := selectedAbsorberFiniteEdgeTower.limitGraph
      (selectedAbsorberFiniteEdgeTower_prefix_of_boundedRanks hb)
    ∀ a b : Nat, IsLeaf K a → IsLeaf K b → a ≠ b →
      IsOneSplit K (K.oneMeetLevel a b) := by
  dsimp only
  intro a b ha hbLeaf hne
  let r := max a b + 1
  obtain ⟨n,hFrame,hPrefix⟩ :=
    selectedAbsorberLimit_exists_full_finite_prefix hb r
  have haR : a < r := by dsimp [r]; omega
  have hbR : b < r := by dsimp [r]; omega
  have han : a < (universalStrongAbsorberTower n).bound := by omega
  have hbn : b < (universalStrongAbsorberTower n).bound := by omega
  have haFinite : IsLeaf (universalStrongAbsorberTower n).graph a :=
    (role_iff_of_literalOldPrefix hPrefix a haR).1.mp ha
  have hbFinite : IsLeaf (universalStrongAbsorberTower n).graph b :=
    (role_iff_of_literalOldPrefix hPrefix b hbR).1.mp hbLeaf
  have hSplit :=
    finiteRoleDiary_s1_unordered
      (universalStrongAbsorberTower n).diary
      a b han hbn haFinite hbFinite hne
  have hMeetEq := oneMeetLevel_eq_of_literalOldPrefix
    hPrefix a b haR hbR
  have hMeetR :
      (universalStrongAbsorberTower n).graph.oneMeetLevel a b < r := by
    have hcap := (universalStrongAbsorberTower n).graph.oneMeetLevel_le_min a b
    omega
  rw [hMeetEq]
  exact (role_iff_of_literalOldPrefix hPrefix _ hMeetR).2.1.mpr hSplit

/-- Full S2 for all ordered pairs of true countable limit leaves,
including both cap alternatives and genuine two-split meets. -/
theorem selectedAbsorberLimit_pair_meets
    (hb : selectedAbsorberFiniteOrderTower.BoundedRanks) :
    let K := selectedAbsorberFiniteEdgeTower.limitGraph
      (selectedAbsorberFiniteEdgeTower_prefix_of_boundedRanks hb)
    ∀ a b c d : Nat, a < b → c < d →
      IsLeaf K a → IsLeaf K b → IsLeaf K c → IsLeaf K d →
      K.twoMeetLevel a b c d = min a c ∨
      K.twoMeetLevel a b c d = 1 ∨
      IsTwoSplit K (K.twoMeetLevel a b c d) := by
  dsimp only
  intro a b c d hab hcd ha hbLeaf hc hd
  let r := max (max a b) (max c d) + 1
  obtain ⟨n,hFrame,hPrefix⟩ :=
    selectedAbsorberLimit_exists_full_finite_prefix hb r
  have haR : a < r := by dsimp [r]; omega
  have hbR : b < r := by dsimp [r]; omega
  have hcR : c < r := by dsimp [r]; omega
  have hdR : d < r := by dsimp [r]; omega
  have hbn : b < (universalStrongAbsorberTower n).bound := by omega
  have hdn : d < (universalStrongAbsorberTower n).bound := by omega
  have haFinite : IsLeaf (universalStrongAbsorberTower n).graph a :=
    (role_iff_of_literalOldPrefix hPrefix a haR).1.mp ha
  have hbFinite : IsLeaf (universalStrongAbsorberTower n).graph b :=
    (role_iff_of_literalOldPrefix hPrefix b hbR).1.mp hbLeaf
  have hcFinite : IsLeaf (universalStrongAbsorberTower n).graph c :=
    (role_iff_of_literalOldPrefix hPrefix c hcR).1.mp hc
  have hdFinite : IsLeaf (universalStrongAbsorberTower n).graph d :=
    (role_iff_of_literalOldPrefix hPrefix d hdR).1.mp hd
  have hSource :=
    (universalStrongAbsorberTower n).diary.pair_meets
      a b c d hab hcd hbn hdn
      haFinite hbFinite hcFinite hdFinite
  have hMeetEq := twoMeetLevel_eq_of_literalOldPrefix
    hPrefix a b c d haR hbR hcR hdR
  have hMeetR :
      (universalStrongAbsorberTower n).graph.twoMeetLevel a b c d < r := by
    have hcap := (universalStrongAbsorberTower n).graph.twoMeetLevel_le_min a b c d
    omega
  rcases hSource with hCap | hOne | hSplit
  · exact Or.inl (hMeetEq.trans hCap)
  · exact Or.inr (Or.inl (hMeetEq.trans hOne))
  · exact Or.inr (Or.inr (by
      rw [hMeetEq]
      exact (role_iff_of_literalOldPrefix hPrefix _ hMeetR).2.2.mpr hSplit))

/-- Precise conditional FULL countable RoleDiary statement.
All V1/V2 existential witnesses come from actual coherent finite
stage embeddings, all universal V/E/S fields from one common
literal finite prefix. No additional existence premise is smuggled
in besides the still-OPEN bounded-rank condition. -/
theorem selectedAbsorberLimit_isRoleDiary_of_boundedRanks
    (hb : selectedAbsorberFiniteOrderTower.BoundedRanks) :
    RoleDiary
      (selectedAbsorberFiniteEdgeTower.limitGraph
        (selectedAbsorberFiniteEdgeTower_prefix_of_boundedRanks hb)) := by
  refine {
    role_valid := selectedAbsorberLimit_role_valid hb
    one_split_coherent := selectedAbsorberLimit_oneSplit_coherent hb
    one_split_witness := selectedAbsorberLimit_oneSplit_witness hb
    two_split_coherent := selectedAbsorberLimit_twoSplit_coherent hb
    two_split_witness := selectedAbsorberLimit_twoSplit_witness hb
    leaf_marker_one := (selectedAbsorberLimit_leaf_markers hb).1
    leaf_marker_two := (selectedAbsorberLimit_leaf_markers hb).2
    edge_ordered := selectedAbsorberFiniteEdgeTower.limitGraph_edge_ordered
      (selectedAbsorberFiniteEdgeTower_prefix_of_boundedRanks hb)
    permitted_edge := selectedAbsorberLimit_permitted_edge hb
    singleton_meets := selectedAbsorberLimit_singleton_meets hb
    pair_meets := selectedAbsorberLimit_pair_meets hb
  }

end DiaryLeafPriority
end ThreeUniformDiaries
