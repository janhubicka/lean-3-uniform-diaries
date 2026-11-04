import ThreeUniformDiaries.DiaryCofinalPrefixNumericMeets
import ThreeUniformDiaries.DiaryFiniteUniversalLeafRange
import ThreeUniformDiaries.DiaryFutureReserveFusion
import ThreeUniformDiaries.DiaryCountableCofinalFiniteSupports

/-!
# Every finite diary support admits an independently reserved copy

This proves a new positive result from established FINITE unavoidability,
not the missing relative extension theorem. To ensure the numerical
FutureOrderReserve, first choose a later canonical finite leaf-meet
support containing the ENTIRE original prefix up through the desired
stage support. Its increasing reindexing then fixes that prefix and
retains its complete edge and type-meet table.

Apply the verified finite full-meet embedding theorem to this larger
finite diary. Restrict the resulting embedding back to the original
stage. Because every intervening source coordinate was retained,
strict monotonicity of the finite embedding supplies the precise
future-order gap inequalities even on the smaller support.

The witnesses for different stages need not agree on any old leaves.
No coherent countable unavoidability or extension of a prescribed
reserved stage follows.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

private theorem finiteSupportGraph_roles_prefix_iff
    (H : Ordered3Graph Nat) (S : Finset Nat)
    (b u : Nat)
    (hPrefix : Finset.range b ⊆ S)
    (hu3 : 3 ≤ u) (hub : u < b) :
    (IsLeaf (finiteSupportGraph H S) u ↔ IsLeaf H u) ∧
    (IsOneSplit (finiteSupportGraph H S) u ↔ IsOneSplit H u) ∧
    (IsTwoSplit (finiteSupportGraph H S) u ↔ IsTwoSplit H u) := by
  have h01 := finiteSupportGraph_edge_prefix_iff
    H S b hPrefix 0 1 u (by omega) (by omega) hub
  have h02 := finiteSupportGraph_edge_prefix_iff
    H S b hPrefix 0 2 u (by omega) (by omega) hub
  constructor
  · unfold IsLeaf
    simp only [h01,h02]
  constructor
  · unfold IsOneSplit
    simp only [h01,h02]
  · unfold IsTwoSplit
    simp only [h01,h02]

/-- Pull a full-meet embedding of a larger complete-prefix finite
reduct back to a genuine RESERVED canonical finite stage. -/
theorem reservedStage_of_completePrefix_finite_embedding
    {H K : Ordered3Graph Nat}
    (F : Nat → Nat) (m b : Nat) (S : Finset Nat)
    (e : Nat → Nat)
    (hBound : ∀ u : Nat,
      u ∈ countableDiaryFiniteSupport H m → u < b)
    (hPrefix : Finset.range b ⊆ S)
    (E : FiniteMeetEmbedding (finiteSupportGraph H S) K S.card e)
    (hRange : ∀ u : Nat,
      3 ≤ u → u < S.card →
      IsLeaf (finiteSupportGraph H S) u →
      ∃ t : Nat, e u = F t) :
    ReservedDiaryStage H K F m e := by
  have hbCard : b ≤ S.card :=
    cardinality_ge_of_prefix_subset S b hPrefix
  let C := finiteSupportGraph H S
  have hRoles (u : Nat) (hu3 : 3 ≤ u) (hub : u < b) :
      (IsLeaf C u ↔ IsLeaf H u) ∧
      (IsOneSplit C u ↔ IsOneSplit H u) ∧
      (IsTwoSplit C u ↔ IsTwoSplit H u) :=
    finiteSupportGraph_roles_prefix_iff H S b u hPrefix hu3 hub
  refine ⟨?_,?_⟩
  · refine {
      ordered := ?_
      marker_zero := E.marker_zero
      marker_one := E.marker_one
      marker_two := E.marker_two
      leaf_role := ?_
      one_split_role := ?_
      two_split_role := ?_
      induced_edge := ?_
      leaf_oneMeet := ?_
      leaf_twoMeet := ?_
      leaf_range := ?_
    }
    · intro u v hu hv huv
      exact E.strictMono huv
    · intro u hu hLeaf
      have hub : u < b := hBound u hu
      exact (E.leaf_iff u hLeaf.1 (by omega)).mpr
        ((hRoles u hLeaf.1 hub).1.mpr hLeaf)
    · intro u hu hOne
      have hub : u < b := hBound u hu
      exact (E.oneSplit_iff u hOne.1 (by omega)).mpr
        ((hRoles u hOne.1 hub).2.1.mpr hOne)
    · intro u hu hTwo
      have hub : u < b := hBound u hu
      exact (E.twoSplit_iff u hTwo.1 (by omega)).mpr
        ((hRoles u hTwo.1 hub).2.2.mpr hTwo)
    · intro x y z hx hy hz hxy hyz
      have hzb : z < b := hBound z hz
      have hOriginal : C.edge x y z ↔ H.edge x y z :=
        finiteSupportGraph_edge_prefix_iff
          H S b hPrefix x y z hxy hyz hzb
      have hEmbedded : K.edge (e x) (e y) (e z) ↔
          C.edge x y z :=
        E.edge_iff x y z hxy hyz (by omega)
      exact hOriginal.symm.trans hEmbedded.symm
    · intro u v hu hv hLeafU hLeafV
      have hub : u < b := hBound u hu
      have hvb : v < b := hBound v hv
      have hMeets := E.oneMeet u v hLeafU.1 (by omega)
        hLeafV.1 (by omega)
      rw [finiteSupportGraph_oneMeet_prefix_eq
        H S b u v hPrefix hub hvb] at hMeets
      exact hMeets
    · intro u v p q hu hv hp hq huv hpq
        hLeafU hLeafV hLeafP hLeafQ
      have hub : u < b := hBound u hu
      have hvb : v < b := hBound v hv
      have hpb : p < b := hBound p hp
      have hqb : q < b := hBound q hq
      have hMeets := E.twoMeet u v p q huv hpq
        hLeafU.1 (by omega) hLeafV.1 (by omega)
        hLeafP.1 (by omega) hLeafQ.1 (by omega)
      rw [finiteSupportGraph_twoMeet_prefix_eq
        H S b u v p q hPrefix huv hpq hvb hqb] at hMeets
      exact hMeets
    · intro u hu hLeaf
      have hub : u < b := hBound u hu
      exact hRange u hLeaf.1 (by omega)
        ((hRoles u hLeaf.1 hub).1.mpr hLeaf)
  · intro x y hx hy hxy
    exact strictMono_nat_gap_bound E.strictMono (Nat.le_of_lt hxy)

/-- Every single finite stage has SOME future-order-reserved full
embedding into the prescribed unordered universal leaf copy.

Crucially, the witness at m is chosen independently of witnesses
at all earlier stages; there is NO compatibility conclusion.
The target G is an actual enumerated generic hypergraph, and F maps
the universal hypergraph into genuine leaves of the full diary K. -/
theorem exists_independent_reserved_stage_in_universal_leaf_range
    {H U K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (hUniversal : Ordered3Graph.CountablyUniversal U)
    (F : Ordered3Graph.UnorderedEmbedding U K)
    (hFleaf : ∀ t : Nat, IsLeaf K (F t))
    (m : Nat) :
    ∃ f : Nat → Nat, ReservedDiaryStage H K F m f := by
  classical
  let M := countableDiaryFiniteSupport H m
  let b : Nat := M.sup id + 3
  have hBound : ∀ u : Nat, u ∈ M → u < b := by
    intro u hu
    have hle : u ≤ M.sup id := by
      simpa only [id_eq] using (Finset.le_sup (f := id) hu)
    dsimp [b]
    omega
  obtain ⟨n,hn⟩ :=
    countableDiaryFiniteSupport_contains_finset DH (Finset.range b)
  let S := countableDiaryFiniteSupport H n
  have hPrefix : Finset.range b ⊆ S := by
    intro u hu
    exact hn u hu
  have DFinite : FiniteRoleDiaryBlock
      (finiteSupportGraph H S) S.card :=
    countableDiaryFiniteSupport_is_finiteDiary DH n
  obtain ⟨f,E,hRange⟩ :=
    exists_finiteDiary_full_embedding_in_universal_leaf_range
      DFinite G hUniversal F hFleaf DK
  refine ⟨f,?_⟩
  exact reservedStage_of_completePrefix_finite_embedding
    F m b S f (by simpa only [M] using hBound)
    hPrefix E hRange

end DiaryLeafPriority
end ThreeUniformDiaries
