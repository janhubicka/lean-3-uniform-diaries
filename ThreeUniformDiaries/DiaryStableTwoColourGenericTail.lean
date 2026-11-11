import ThreeUniformDiaries.DiaryRelativeMultiColourTailObstruction
import ThreeUniformDiaries.DiarySingletonColourCofinalCone

/-!
# Track C: two distinct stable cofinal mixed-colour branches in a generic leaf range

English-first proof/adversarial audit:
  janhubicka/3-uniform-diaries PR #288

In the ORIGINAL unordered generic true-leaf subcopy F, each fixed
old pair F i < F j < B admits positive and negative future incidences
arbitrarily far out. Because the palette of COMPLETE singleton colours
at B is finite, each sign has ONE fixed colour occurring arbitrarily
far out. The two stable colours must differ because the protected
old-pair incidence is a test entry of every B-colour.

This is a positive finite multicolour branching fact, not relative
E2/E3 realization, preservation of numeric S1/S2 meets, or a
persistent next-leaf survivor.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Two distinct complete mixed singleton masks are each realized
numerically cofinally in the SAME prescribed induced generic true-leaf
range: one with positive and one with negative incidence over a fixed
target-ordered old pair F i < F j < B.

The two fixed finite masks are chosen BEFORE the numerical bound M.
Neither colour class is claimed to be a generic induced subcopy. -/
theorem exists_two_cofinal_opposite_generic_leaf_colour_fibres
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : _root_.ThreeUniformDiaries.Ordered3Graph.UnorderedEmbedding G.graph K)
    (hLeaves : ∀ n : Nat, IsLeaf K (F n))
    (i j B : Nat) (hij : F i < F j) (hjB : F j < B) :
    ∃ cPos cNeg : Fin B → Fin B → Bool,
      cPos ≠ cNeg ∧
      (∀ M : Nat, ∃ t : Nat,
        M < F t ∧ B < F t ∧ IsLeaf K (F t) ∧
        K.edge (F i) (F j) (F t) ∧
        DiaryLowerBoundColors.singletonColour K B (F t) = cPos) ∧
      (∀ M : Nat, ∃ t : Nat,
        M < F t ∧ B < F t ∧ IsLeaf K (F t) ∧
        ¬ K.edge (F i) (F j) (F t) ∧
        DiaryLowerBoundColors.singletonColour K B (F t) = cNeg) := by
  classical
  let C := Fin B → Fin B → Bool
  let Rpos : C → Nat → Prop := fun c M =>
    ∃ t : Nat, M < F t ∧ B < F t ∧ IsLeaf K (F t) ∧
      K.edge (F i) (F j) (F t) ∧
      DiaryLowerBoundColors.singletonColour K B (F t) = c
  let Rneg : C → Nat → Prop := fun c M =>
    ∃ t : Nat, M < F t ∧ B < F t ∧ IsLeaf K (F t) ∧
      ¬ K.edge (F i) (F j) (F t) ∧
      DiaryLowerBoundColors.singletonColour K B (F t) = c
  have hDownPos : ∀ c : C, ∀ N M : Nat,
      M ≤ N → Rpos c N → Rpos c M := by
    intro c N M hMN
    rintro ⟨t, ht, hBt, hLeaf, hEdge, hColour⟩
    exact ⟨t, lt_of_le_of_lt hMN ht, hBt, hLeaf, hEdge, hColour⟩
  have hDownNeg : ∀ c : C, ∀ N M : Nat,
      M ≤ N → Rneg c N → Rneg c M := by
    intro c N M hMN
    rintro ⟨t, ht, hBt, hLeaf, hEdge, hColour⟩
    exact ⟨t, lt_of_le_of_lt hMN ht, hBt, hLeaf, hEdge, hColour⟩
  have hCoverPos : ∀ M : Nat, ∃ c : C,
      c ∈ (Finset.univ : Finset C) ∧ Rpos c M := by
    intro M
    obtain ⟨t, ht, hPattern⟩ :=
      exists_outer_generic_vertex_positive_on_bounded_pairs
        G K F B (max B M)
    have hMt : M < F t :=
      lt_of_le_of_lt (le_max_right B M) ht
    have hBt : B < F t :=
      lt_of_le_of_lt (le_max_left B M) ht
    exact ⟨DiaryLowerBoundColors.singletonColour K B (F t),
      Finset.mem_univ _, t, hMt, hBt, hLeaves t,
      hPattern i j hij hjB, rfl⟩
  have hCoverNeg : ∀ M : Nat, ∃ c : C,
      c ∈ (Finset.univ : Finset C) ∧ Rneg c M := by
    intro M
    obtain ⟨t, ht, hPattern⟩ :=
      exists_outer_generic_vertex_negative_on_bounded_pairs
        G K F B (max B M)
    have hMt : M < F t :=
      lt_of_le_of_lt (le_max_right B M) ht
    have hBt : B < F t :=
      lt_of_le_of_lt (le_max_left B M) ht
    exact ⟨DiaryLowerBoundColors.singletonColour K B (F t),
      Finset.mem_univ _, t, hMt, hBt, hLeaves t,
      hPattern i j hij hjB, rfl⟩
  obtain ⟨cPos, _hMemPos, hAllPos⟩ :=
    finite_choice_persistent_of_downward_type
      (Finset.univ : Finset C) Rpos hDownPos hCoverPos
  obtain ⟨cNeg, _hMemNeg, hAllNeg⟩ :=
    finite_choice_persistent_of_downward_type
      (Finset.univ : Finset C) Rneg hDownNeg hCoverNeg
  have hDistinct : cPos ≠ cNeg := by
    intro hEq
    obtain ⟨p, _hp, _hBp, _hLeafP, hEdgeP, hColP⟩ := hAllPos 0
    obtain ⟨q, _hq, _hBq, _hLeafQ, hNoEdgeQ, hColQ⟩ := hAllNeg 0
    have hSameColour :
        DiaryLowerBoundColors.singletonColour K B (F p) =
          DiaryLowerBoundColors.singletonColour K B (F q) := by
      calc
        DiaryLowerBoundColors.singletonColour K B (F p) = cPos := hColP
        _ = cNeg := hEq
        _ = DiaryLowerBoundColors.singletonColour K B (F q) := hColQ.symm
    have hSameEdge :=
      same_singletonColour_forces_same_old_pair_edge
        K B (F i) (F j) (F p) (F q) hij hjB hSameColour
    exact hNoEdgeQ (hSameEdge.mp hEdgeP)
  refine ⟨cPos, cNeg, hDistinct, ?_, ?_⟩
  · intro M
    exact hAllPos M
  · intro M
    exact hAllNeg M

/-- Both fixed colour branches can simultaneously be required to be
late in the original generic SOURCE indices and in TARGET numerical
positions. This follows from finite-prefix maximum bounds for any
function F; no monotonicity of F is assumed. -/
theorem exists_two_cofinal_index_and_image_generic_leaf_colour_fibres
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : _root_.ThreeUniformDiaries.Ordered3Graph.UnorderedEmbedding G.graph K)
    (hLeaves : ∀ n : Nat, IsLeaf K (F n))
    (i j B : Nat) (hij : F i < F j) (hjB : F j < B) :
    ∃ cPos cNeg : Fin B → Fin B → Bool,
      cPos ≠ cNeg ∧
      (∀ N M : Nat, ∃ t : Nat,
        N ≤ t ∧ M < F t ∧ B < F t ∧ IsLeaf K (F t) ∧
        K.edge (F i) (F j) (F t) ∧
        DiaryLowerBoundColors.singletonColour K B (F t) = cPos) ∧
      (∀ N M : Nat, ∃ t : Nat,
        N ≤ t ∧ M < F t ∧ B < F t ∧ IsLeaf K (F t) ∧
        ¬ K.edge (F i) (F j) (F t) ∧
        DiaryLowerBoundColors.singletonColour K B (F t) = cNeg) := by
  classical
  obtain ⟨cPos, cNeg, hNe, hPos, hNeg⟩ :=
    exists_two_cofinal_opposite_generic_leaf_colour_fibres
      G K F hLeaves i j B hij hjB
  refine ⟨cPos, cNeg, hNe, ?_, ?_⟩
  · intro N M
    let L := max M ((Finset.range N).sup (fun t => F t))
    obtain ⟨t, ht, hBt, hLeaf, hEdge, hCol⟩ := hPos L
    have hML : M ≤ L := le_max_left _ _
    have hSupL : (Finset.range N).sup (fun t => F t) ≤ L :=
      le_max_right _ _
    have hIndex : N ≤ t := by
      by_contra hBad
      have htN : t < N := by omega
      have hBound : F t ≤ (Finset.range N).sup (fun t => F t) :=
        Finset.le_sup (f := fun t => F t) (Finset.mem_range.mpr htN)
      omega
    exact ⟨t, hIndex, lt_of_le_of_lt hML ht, hBt, hLeaf, hEdge, hCol⟩
  · intro N M
    let L := max M ((Finset.range N).sup (fun t => F t))
    obtain ⟨t, ht, hBt, hLeaf, hEdge, hCol⟩ := hNeg L
    have hML : M ≤ L := le_max_left _ _
    have hSupL : (Finset.range N).sup (fun t => F t) ≤ L :=
      le_max_right _ _
    have hIndex : N ≤ t := by
      by_contra hBad
      have htN : t < N := by omega
      have hBound : F t ≤ (Finset.range N).sup (fun t => F t) :=
        Finset.le_sup (f := fun t => F t) (Finset.mem_range.mpr htN)
      omega
    exact ⟨t, hIndex, lt_of_le_of_lt hML ht, hBt, hLeaf, hEdge, hCol⟩

end DiaryLeafPriority
end ThreeUniformDiaries
