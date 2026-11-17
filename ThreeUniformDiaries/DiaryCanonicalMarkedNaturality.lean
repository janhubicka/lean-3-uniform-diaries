import ThreeUniformDiaries.DiaryCanonicalMarkedRawSourceGraph
import ThreeUniformDiaries.DiaryCanonicalMarkedNestedComplete

/-!
# Canonical marked-diary restriction along arbitrary labelled subcopies

This is the essential naturality statement at the level of REAL
leaf tuples in one full RoleDiary K. Given a labelled induced
A-copy on genuine leaves, a finite label map i and an actual
induced B-copy on the selected leaves, the intrinsic raw
restriction of the complete marked A-source is LITERALLY
the canonical marked B-source.

The proof uses the independently validated COMPLETE nested
finite support/graph/marked-rank theorem, plus the exact source
size/picture of rawRestrict. No assumption about countable
diary unavoidability, BRS or abstract Safe fusion is introduced.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open DiaryLeafPriority

/-- Exact raw restriction of the complete canonical A-source
to the canonical B-source of the corresponding induced subcopy.
The subcopy map i need not be increasing on label indices. -/
theorem canonicalMarkedSourceOfLeaves_rawRestrict
    {K : Ordered3Graph Nat} (D : RoleDiary K)
    {a b : Nat} (A : EnumNode a) (B : EnumNode b)
    (v : Fin a → Nat)
    (hLeaf : ∀ j : Fin a, IsLeaf K (v j))
    (hA : IsInducedLabelledCopy A K v)
    (i : Fin b → Fin a)
    (hB : IsInducedLabelledCopy B K (fun j => v (i j))) :
    (canonicalMarkedSourceOfLeaves D A v hLeaf hA).rawRestrict i =
      canonicalMarkedSourceOfLeaves D B
        (fun j => v (i j)) (fun j => hLeaf (i j)) hB := by
  classical
  let w : Fin b → Nat := fun j => v (i j)
  let L : Finset Nat :=
    (Finset.univ : Finset (Fin a)).image v
  let L' : Finset Nat :=
    (Finset.univ : Finset (Fin b)).image w
  let S : Finset Nat := finiteLeafMeetSupport K L
  let T : Finset Nat := finiteLeafMeetSupport K L'
  let r : Nat → Nat := finiteSupportRank S
  let H : Ordered3Graph Nat := finiteSupportGraph K S
  let V : Finset Nat := finiteLeafMeetSupport H (L'.image r)
  let P : MarkedFiniteSource 0 a :=
    canonicalMarkedSourceOfLeaves D A v hLeaf hA
  let R : MarkedFiniteSource 0 b := P.rawRestrict i
  have hL : ∀ u : Nat, u ∈ L → IsLeaf K u := by
    intro u hu
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hu
    exact hLeaf j
  have hSub : L' ⊆ L := by
    intro u hu
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hu
    exact Finset.mem_image.mpr
      ⟨i j, Finset.mem_univ _, rfl⟩
  have hTS : T ⊆ S := finiteLeafMeetSupport_mono K L' L hSub
  have hNested :
      V = T.image r ∧
        finiteSupportGraph H V = finiteSupportGraph K T ∧
        (∀ u : Nat, u ∈ L' →
          finiteSupportRank V (r u) = finiteSupportRank T u) := by
    exact finiteLeafMeetSupport_nested_complete D L L' hL hSub
  have hV : markedRestrictionSupport P i = V := by
    exact canonicalMarkedSourceOfLeaves_restriction_support
      D A v hLeaf hA i
  have hRsize : R.source.k + 1 = T.card := by
    have hSize := P.rawRestrict_source_size i
    change R.source.k + 1 =
      (markedRestrictionSupport P i).card at hSize
    rw [hV] at hSize
    calc
      R.source.k + 1 = V.card := hSize
      _ = (T.image r).card := congrArg Finset.card hNested.1
      _ = T.card := finiteSupportRank_image_card S T hTS
  have hPGraph : P.source.picture.toOrdered3Graph = H :=
    (canonicalMarkedSourceOfLeaves_spec D A v hLeaf hA).2.2.1
  have hRgraph : R.source.picture.toOrdered3Graph =
      finiteSupportGraph K T := by
    have hRaw := P.rawRestrict_source_graph i
    change R.source.picture.toOrdered3Graph =
      finiteSupportGraph P.source.picture.toOrdered3Graph
        (markedRestrictionSupport P i) at hRaw
    calc
      R.source.picture.toOrdered3Graph =
          finiteSupportGraph P.source.picture.toOrdered3Graph
            (markedRestrictionSupport P i) := hRaw
      _ = finiteSupportGraph H V := by
        rw [hPGraph, hV]
      _ = finiteSupportGraph K T := hNested.2.1
  have hRindex : ∀ j : Fin b,
      finiteSupportIndex T (R.marked j).val = w j := by
    intro j
    have hPmark :
        (P.marked (i j)).val = r (w j) :=
      canonicalMarkedSourceOfLeaves_marked_rank
        D A v hLeaf hA (i j)
    have hRaw := P.rawRestrict_marked_rank i j
    change (R.marked j).val =
      finiteSupportRank (markedRestrictionSupport P i)
        (P.marked (i j)).val at hRaw
    have hRank :
        (R.marked j).val = finiteSupportRank T (w j) := by
      calc
        (R.marked j).val =
            finiteSupportRank (markedRestrictionSupport P i)
              (P.marked (i j)).val := hRaw
        _ = finiteSupportRank V (r (w j)) := by
          rw [hV, hPmark]
        _ = finiteSupportRank T (w j) :=
          hNested.2.2 (w j)
            (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)
    rw [hRank]
    exact (finiteSupportRank_spec T (w j)
      (mem_finiteLeafMeetSupport_leaf K L' (w j)
        (Finset.mem_image.mpr ⟨j, Finset.mem_univ _,rfl⟩))).2
  have hEq := canonicalMarkedSourceOfLeaves_eq_of_spec
    D B w (fun j => hLeaf (i j)) hB R
    hRsize hRgraph hRindex
  exact hEq.symm

/-- The raw restricted code is a GENUINE marked B-diary when
the selected labelled tuple is really an induced B-copy. -/
theorem canonicalMarkedSource_rawRestrict_genuine
    {K : Ordered3Graph Nat} (D : RoleDiary K)
    {a b : Nat} (A : EnumNode a) (B : EnumNode b)
    (v : Fin a → Nat)
    (hLeaf : ∀ j : Fin a, IsLeaf K (v j))
    (hA : IsInducedLabelledCopy A K v)
    (i : Fin b → Fin a)
    (hB : IsInducedLabelledCopy B K (fun j => v (i j))) :
    (canonicalMarkedSourceOfLeaves D A v hLeaf hA).rawRestrict i ∈
      allGenuineMarkedDiaryFinset B := by
  rw [canonicalMarkedSourceOfLeaves_rawRestrict
    D A B v hLeaf hA i hB]
  exact (canonicalMarkedSourceOfLeaves_spec
    D B (fun j => v (i j)) (fun j => hLeaf (i j)) hB).1

end ATRFiniteDecoder
end ThreeUniformDiaries
