import ThreeUniformDiaries.DiaryPrediaryInsertionInvariant
import ThreeUniformDiaries.DiaryRoleAxioms

/-!
# The actual new one-split edges in pre-diary completion

At a defective singleton meet ell, the manuscript inserts a new
role-one vertex and connects it to precisely one OLD
singleton-type class at the next cut ell+1.

This is the relational construction, not merely a Boolean
code. We verify that the fresh marker has 1-split role,
that the old graph is still induced, and that the chosen
class receives precisely its intended split edges.
The remaining V1/V2 coherence, the meet calculation,
and the termination of repeated insertion are separate
obligations.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Permitted new edges involving ell: its role marker and
realisation of one selected old 1-type class of leaves. -/
def oneClassExtra
    (H : Ordered3Graph Nat) (ell anchor : Nat)
    (x y z : Nat) : Prop :=
  x = 0 ∧
    ((y = 1 ∧ z = ell) ∨
     (y = ell ∧ ∃ u : Nat,
       DiaryLeafPriority.IsLeaf H u ∧
       H.SameOneTypeBelow (ell + 1) anchor u ∧
       z = insertShift ell u))

/-- The concrete first case of the manuscript's split insertion. -/
def insertOneClass
    (H : Ordered3Graph Nat) (ell anchor : Nat) :
    Ordered3Graph Nat :=
  H.insertWithNewEdges ell (H.oneClassExtra ell anchor)

/-- The new vertex is assigned exactly the 1-split marker role. -/
theorem insertOneClass_isOneSplit
    (H : Ordered3Graph Nat) (ell anchor : Nat)
    (hell : 3 ≤ ell) :
    DiaryLeafPriority.IsOneSplit (H.insertOneClass ell anchor) ell := by
  refine ⟨hell, ?_, ?_⟩
  · simp [insertOneClass, insertWithNewEdges, oneClassExtra,
      isolatedInsert]
  · have h2 : (2 : Nat) ≠ ell := by omega
    have h1 : (1 : Nat) ≠ ell := by omega
    simp [insertOneClass, insertWithNewEdges, oneClassExtra,
      isolatedInsert, h2, h1]

/-- No original edges or nonedges are changed by selecting a class. -/
theorem insertOneClass_induced
    (H : Ordered3Graph Nat) (ell anchor a b c : Nat) :
    (H.insertOneClass ell anchor).edge
      (insertShift ell a) (insertShift ell b)
      (insertShift ell c) ↔ H.edge a b c := by
  exact H.insertWithNewEdges_edge_iff_image ell
    (H.oneClassExtra ell anchor) a b c

/-- Every old vertex retains its exact marker role. -/
theorem insertOneClass_oldLeaf_iff
    (H : Ordered3Graph Nat) (ell anchor u : Nat)
    (hell : 3 ≤ ell) :
    DiaryLeafPriority.IsLeaf (H.insertOneClass ell anchor)
      (insertShift ell u) ↔ DiaryLeafPriority.IsLeaf H u := by
  have h0 : insertShift ell 0 = 0 :=
    insertShift_before ell 0 (by omega)
  have h1 : insertShift ell 1 = 1 :=
    insertShift_before ell 1 (by omega)
  have h2 : insertShift ell 2 = 2 :=
    insertShift_before ell 2 (by omega)
  have he1 := H.insertOneClass_induced ell anchor 0 1 u
  have he2 := H.insertOneClass_induced ell anchor 0 2 u
  simp only [h0, h1] at he1
  simp only [h0, h2] at he2
  constructor
  · rintro ⟨hu, hA, hB⟩
    refine ⟨?_, ?_, ?_⟩
    · unfold insertShift at hu
      split_ifs at hu <;> omega
    · exact fun h => hA (he1.mpr h)
    · exact fun h => hB (he2.mpr h)
  · rintro ⟨hu, hA, hB⟩
    refine ⟨?_, ?_, ?_⟩
    · unfold insertShift
      split_ifs <;> omega
    · exact fun h => hA (he1.mp h)
    · exact fun h => hB (he2.mp h)

/-- An old leaf is positive at the inserted 1-split exactly
when it has the selected OLD 1-type at ell+1. -/
theorem insertOneClass_edge_iff
    (H : Ordered3Graph Nat) (ell anchor u : Nat)
    (hell : 3 ≤ ell)
    (hu : DiaryLeafPriority.IsLeaf H u) :
    (H.insertOneClass ell anchor).edge
      0 ell (insertShift ell u) ↔
        H.SameOneTypeBelow (ell + 1) anchor u := by
  have h1 : ell ≠ 1 := by omega
  have hinj : Function.Injective (insertShift ell) :=
    (insertShift_strictMono ell).injective
  constructor
  · intro h
    rcases h with hOld | ⟨_, hExtra⟩
    · exact False.elim (by simpa [insertOneClass, insertWithNewEdges,
        isolatedInsert] using hOld)
    · rcases hExtra with ⟨hx, hRole | hClass⟩
      · exact False.elim (h1 hRole.1.symm)
      · rcases hClass with ⟨_, w, hwLeaf, hwSame, hwShift⟩
        have heq : u = w := hinj hwShift
        simpa [heq] using hwSame
  · intro hs
    change (H.isolatedInsert ell).edge 0 ell (insertShift ell u) ∨
      ((0 = ell ∨ ell = ell ∨ insertShift ell u = ell) ∧
        H.oneClassExtra ell anchor 0 ell (insertShift ell u))
    apply Or.inr
    constructor
    · simp
    · exact ⟨rfl, Or.inr ⟨rfl, u, hu, hs, rfl⟩⟩

end Ordered3Graph
end ThreeUniformDiaries
