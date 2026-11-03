import ThreeUniformDiaries.DiarySharpUnlabelledConditionalUpper

/-!
# Track C: a genuine diary leaf reduct is an increasing presentation of A

The verified genuine marked family uses arbitrary labelled copies of
the UNORDERED source A. The intended diary degree counts increasing
ordered presentations. This file explicitly connects these notions.

Every genuine marking is an injective A-labelling exhausting ALL
bounded leaves. Consequently the true finite leaf set has exactly a
elements. Its canonical increasing order is the orderIsoOfFin of that
finite set. Comparing a chosen marking with that increasing order
produces a literal permutation of Fin a.

The unordered induced A-edge predicate transports through that
permutation to the increasing leaf coordinates of the finite diary.
Thus each unmarked diary shape really does carry an increasing
presentation of the unordered A, rather than merely an arbitrary
uninterpreted partition label.

This does not assert that every ordered presentation is realised
by a diary, nor identify any extra published diary equivalence
relation. No Ramsey, source-cover or countable unavoidability enters.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- The genuine source leaf set has exactly the same cardinality as
the prescribed finite A, since the marking is injective AND covers
all genuine source leaves. -/
theorem genuineMarkedDiaryShape_leafPositions_card
    {a : Nat} (A : EnumNode a)
    (T : MarkedFiniteSource 0 a)
    (hShape : IsGenuineMarkedDiaryShape A T) :
    T.source.leafPositions.card = a := by
  classical
  have hImage :=
    genuineMarkedDiaryShape_markedLeaves_eq_positions A T hShape
  have hCopy :
      IsFiniteLabelledCopy
        A.toOrdered3Graph T.source.picture.toOrdered3Graph a
        (fun i => (T.marked i).val) :=
    hShape.2.1
  have hInject : Function.Injective T.marked := by
    intro i j hij
    exact hCopy.1 (congrArg Fin.val hij)
  calc
    T.source.leafPositions.card =
        ((Finset.univ : Finset (Fin a)).image T.marked).card :=
      congrArg Finset.card hImage.symm
    _ = (Finset.univ : Finset (Fin a)).card :=
      Finset.card_image_of_injective Finset.univ hInject
    _ = a := by simp

/-- The canonical increasing enumeration of the EXACT source
leaf set, indexed by the a elements of A. -/
noncomputable def genuineMarkedDiaryShape_leafOrderIso
    {a : Nat} (A : EnumNode a)
    (T : MarkedFiniteSource 0 a)
    (hShape : IsGenuineMarkedDiaryShape A T) :
    Fin a ≃o ↑T.source.leafPositions :=
  T.source.leafPositions.orderIsoOfFin
    (genuineMarkedDiaryShape_leafPositions_card A T hShape)

/-- Comparing the arbitrary labelled source marking with the
increasing source-leaf order gives a true permutation of Fin a.
This permutation contains the complete ordering information
which must be retained in the diary count of unordered A. -/
noncomputable def genuineMarkedDiaryShape_labelRankPerm
    {a : Nat} (A : EnumNode a)
    (T : MarkedFiniteSource 0 a)
    (hShape : IsGenuineMarkedDiaryShape A T) :
    Equiv.Perm (Fin a) := by
  classical
  let E := genuineMarkedDiaryShape_leafOrderIso A T hShape
  have hImage :=
    genuineMarkedDiaryShape_markedLeaves_eq_positions A T hShape
  have hMem (i : Fin a) :
      T.marked i ∈ T.source.leafPositions := by
    rw [← hImage]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  let rank : Fin a → Fin a :=
    fun i => E.symm ⟨T.marked i, hMem i⟩
  have hCopy :
      IsFiniteLabelledCopy
        A.toOrdered3Graph T.source.picture.toOrdered3Graph a
        (fun i => (T.marked i).val) := hShape.2.1
  have hinj : Function.Injective rank := by
    intro i j hij
    have hsub :
        (⟨T.marked i, hMem i⟩ : ↑T.source.leafPositions) =
          ⟨T.marked j, hMem j⟩ :=
      E.symm.injective hij
    exact hCopy.1 (congrArg Fin.val
      (congrArg Subtype.val hsub))
  exact Equiv.ofBijective rank
    ⟨hinj, Finite.surjective_of_injective hinj⟩

/-- The rank permutation's defining equation: the leaf at rank
sigma(i) is literally the source vertex carrying label i. -/
theorem genuineMarkedDiaryShape_labelRankPerm_apply
    {a : Nat} (A : EnumNode a)
    (T : MarkedFiniteSource 0 a)
    (hShape : IsGenuineMarkedDiaryShape A T)
    (i : Fin a) :
    ((genuineMarkedDiaryShape_leafOrderIso A T hShape)
      ((genuineMarkedDiaryShape_labelRankPerm A T hShape) i)).val =
      T.marked i := by
  classical
  have hImage :=
    genuineMarkedDiaryShape_markedLeaves_eq_positions A T hShape
  have hMem : T.marked i ∈ T.source.leafPositions := by
    rw [← hImage]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  change ((genuineMarkedDiaryShape_leafOrderIso A T hShape)
    ((genuineMarkedDiaryShape_leafOrderIso A T hShape).symm
      ⟨T.marked i, hMem⟩)).val = T.marked i
  simp

/-- Exact unordered induced-edge transport between the arbitrary
labelling of A and its canonical increasing source-leaf order.
The source labels are NOT assumed numerically increasing. -/
theorem genuineMarkedDiaryShape_labelRank_edge_iff
    {a : Nat} (A : EnumNode a)
    (T : MarkedFiniteSource 0 a)
    (hShape : IsGenuineMarkedDiaryShape A T)
    (i j k : Fin a) :
    A.toOrdered3Graph.unorderedEdge i.val j.val k.val ↔
      T.source.picture.toOrdered3Graph.unorderedEdge
        (((genuineMarkedDiaryShape_leafOrderIso A T hShape)
          ((genuineMarkedDiaryShape_labelRankPerm A T hShape) i)).val).val
        (((genuineMarkedDiaryShape_leafOrderIso A T hShape)
          ((genuineMarkedDiaryShape_labelRankPerm A T hShape) j)).val).val
        (((genuineMarkedDiaryShape_leafOrderIso A T hShape)
          ((genuineMarkedDiaryShape_labelRankPerm A T hShape) k)).val).val := by
  have hCopy :
      IsFiniteLabelledCopy
        A.toOrdered3Graph T.source.picture.toOrdered3Graph a
        (fun t => (T.marked t).val) := hShape.2.1
  rw [genuineMarkedDiaryShape_labelRankPerm_apply A T hShape i,
    genuineMarkedDiaryShape_labelRankPerm_apply A T hShape j,
    genuineMarkedDiaryShape_labelRankPerm_apply A T hShape k]
  exact hCopy.2 i j k

/-- In increasing order, the source diary's genuine leaves realise
the finite hypergraph A with vertex labels permuted by the actual
inverse rank permutation. This is precisely the increasing ordered
presentation needed to interpret a diary of UNORDERED A. -/
theorem genuineMarkedDiaryShape_increasing_presentation
    {a : Nat} (A : EnumNode a)
    (T : MarkedFiniteSource 0 a)
    (hShape : IsGenuineMarkedDiaryShape A T)
    (i j k : Fin a) :
    A.toOrdered3Graph.unorderedEdge
      ((genuineMarkedDiaryShape_labelRankPerm A T hShape).symm i).val
      ((genuineMarkedDiaryShape_labelRankPerm A T hShape).symm j).val
      ((genuineMarkedDiaryShape_labelRankPerm A T hShape).symm k).val ↔
    T.source.picture.toOrdered3Graph.unorderedEdge
      (((genuineMarkedDiaryShape_leafOrderIso A T hShape) i).val).val
      (((genuineMarkedDiaryShape_leafOrderIso A T hShape) j).val).val
      (((genuineMarkedDiaryShape_leafOrderIso A T hShape) k).val).val := by
  have h :=
    genuineMarkedDiaryShape_labelRank_edge_iff A T hShape
      ((genuineMarkedDiaryShape_labelRankPerm A T hShape).symm i)
      ((genuineMarkedDiaryShape_labelRankPerm A T hShape).symm j)
      ((genuineMarkedDiaryShape_labelRankPerm A T hShape).symm k)
  simpa only [Equiv.apply_symm_apply] using h

end ATRFiniteDecoder
end ThreeUniformDiaries
