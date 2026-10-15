import ThreeUniformDiaries.DiaryPrediaryInsertionInvariant
import ThreeUniformDiaries.DiaryRoleAxioms

/-!
# The actual new two-split edges in pre-diary completion

The second insertion case adds a new role-two vertex ell,
then connects it to ordered leaf pairs representing one
selected OLD full pair-type class at the cut ell+1.

We verify marker role, exact inducedness of old copies, and
the chosen positive pair-class incidence at the new level.
These are necessary local steps, not full pre-diary coherence,
meet preservation or termination.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- New role-two marker and only one old ordered leaf-pair
type class, with the pair genuinely above the insertion cut. -/
def twoClassExtra
    (H : Ordered3Graph Nat)
    (ell anchor₀ anchor₁ x y z : Nat) : Prop :=
  (x = 0 ∧ y = 2 ∧ z = ell) ∨
  (x = ell ∧ ∃ u v : Nat,
    ell < u ∧ u < v ∧
    DiaryLeafPriority.IsLeaf H u ∧
    DiaryLeafPriority.IsLeaf H v ∧
    H.SameTwoTypeBelow (ell + 1) anchor₀ anchor₁ u v ∧
    y = insertShift ell u ∧ z = insertShift ell v)

/-- The manuscript's selected 2-split class insertion. -/
def insertTwoClass
    (H : Ordered3Graph Nat)
    (ell anchor₀ anchor₁ : Nat) : Ordered3Graph Nat :=
  H.insertWithNewEdges ell (H.twoClassExtra ell anchor₀ anchor₁)

/-- The new vertex has exactly the role of a 2-split. -/
theorem insertTwoClass_isTwoSplit
    (H : Ordered3Graph Nat) (ell anchor₀ anchor₁ : Nat)
    (hell : 3 ≤ ell) :
    DiaryLeafPriority.IsTwoSplit
      (H.insertTwoClass ell anchor₀ anchor₁) ell := by
  refine ⟨hell, ?_, ?_⟩
  · have h1 : (1 : Nat) ≠ 2 := by omega
    have h0 : (0 : Nat) ≠ ell := by omega
    have he : (1 : Nat) ≠ ell := by omega
    simp [insertTwoClass, insertWithNewEdges,
      twoClassExtra, isolatedInsert, h1, h0, he]
  · simp [insertTwoClass, insertWithNewEdges,
      twoClassExtra, isolatedInsert]

/-- The first structural requirement: old induced copies survive. -/
theorem insertTwoClass_induced
    (H : Ordered3Graph Nat)
    (ell anchor₀ anchor₁ a b c : Nat) :
    (H.insertTwoClass ell anchor₀ anchor₁).edge
      (insertShift ell a) (insertShift ell b)
      (insertShift ell c) ↔ H.edge a b c := by
  exact H.insertWithNewEdges_edge_iff_image ell
    (H.twoClassExtra ell anchor₀ anchor₁) a b c

/-- Old leaf roles are unchanged, even though the new level
creates additional pair incidences. -/
theorem insertTwoClass_oldLeaf_iff
    (H : Ordered3Graph Nat)
    (ell anchor₀ anchor₁ u : Nat)
    (hell : 3 ≤ ell) :
    DiaryLeafPriority.IsLeaf
      (H.insertTwoClass ell anchor₀ anchor₁)
      (insertShift ell u) ↔ DiaryLeafPriority.IsLeaf H u := by
  have h0 : insertShift ell 0 = 0 :=
    insertShift_before ell 0 (by omega)
  have h1 : insertShift ell 1 = 1 :=
    insertShift_before ell 1 (by omega)
  have h2 : insertShift ell 2 = 2 :=
    insertShift_before ell 2 (by omega)
  have he1 := H.insertTwoClass_induced ell anchor₀ anchor₁ 0 1 u
  have he2 := H.insertTwoClass_induced ell anchor₀ anchor₁ 0 2 u
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

/-- Exact incidence of the fresh split with each old ordered
leaf pair: one iff that pair belongs to the chosen OLD
full 2-type class through ell+1. -/
theorem insertTwoClass_edge_iff
    (H : Ordered3Graph Nat)
    (ell anchor₀ anchor₁ u v : Nat)
    (hell : 3 ≤ ell) (hEllU : ell < u) (hUV : u < v)
    (hu : DiaryLeafPriority.IsLeaf H u)
    (hv : DiaryLeafPriority.IsLeaf H v) :
    (H.insertTwoClass ell anchor₀ anchor₁).edge
      ell (insertShift ell u) (insertShift ell v) ↔
      H.SameTwoTypeBelow (ell + 1) anchor₀ anchor₁ u v := by
  have hinj : Function.Injective (insertShift ell) :=
    (insertShift_strictMono ell).injective
  have h0 : ell ≠ 0 := by omega
  constructor
  · intro h
    rcases h with hOld | ⟨_, hExtra⟩
    · exact False.elim (by simpa [insertTwoClass, insertWithNewEdges,
        isolatedInsert] using hOld)
    · rcases hExtra with hRole | hClass
      · exact False.elim (h0 hRole.1)
      · rcases hClass with
          ⟨_, u', v', hEllU', hUV', hu', hv', hType, hy, hz⟩
        have heU : u = u' := hinj hy
        have heV : v = v' := hinj hz
        simpa [heU, heV] using hType
  · intro hs
    change (H.isolatedInsert ell).edge ell
        (insertShift ell u) (insertShift ell v) ∨
      ((ell = ell ∨ insertShift ell u = ell ∨
        insertShift ell v = ell) ∧
       H.twoClassExtra ell anchor₀ anchor₁ ell
         (insertShift ell u) (insertShift ell v))
    apply Or.inr
    constructor
    · simp
    · exact Or.inr ⟨rfl, u, v, hEllU, hUV,
        hu, hv, hs, rfl, rfl⟩

end Ordered3Graph
end ThreeUniformDiaries
