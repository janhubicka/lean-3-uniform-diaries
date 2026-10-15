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
       ell ≤ u ∧ DiaryLeafPriority.IsLeaf H u ∧
       H.SameOneTypeBelow (ell + 1) anchor u ∧
       z = insertShift ell u))

/-- Every NEW 1-split hyperedge is on three strictly increasing
vertices; leaf witnesses at or before the old cut are properly
handled by shifting the old tail up one level. -/
theorem oneClassExtra_ordered
    (H : Ordered3Graph Nat) (ell anchor x y z : Nat)
    (hell : 3 ≤ ell)
    (he : H.oneClassExtra ell anchor x y z) :
    x < y ∧ y < z := by
  rcases he with ⟨hx, hRole | hSplit⟩
  · rcases hRole with ⟨hy, hz⟩
    subst x
    subst y
    subst z
    omega
  · rcases hSplit with ⟨hy, u, hu, hLeaf, hClass, hz⟩
    subst x
    subst y
    subst z
    have hShift : ell < insertShift ell u := by
      unfold insertShift
      split_ifs <;> omega
    omega

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
    (hell : 3 ≤ ell) (hEllU : ell ≤ u)
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
      · exact False.elim (h1 hRole.1)
      · rcases hClass with ⟨_, w, hwBound, hwLeaf, hwSame, hwShift⟩
        have heq : u = w := hinj hwShift
        simpa [heq] using hwSame
  · intro hs
    change (H.isolatedInsert ell).edge 0 ell (insertShift ell u) ∨
      ((0 = ell ∨ ell = ell ∨ insertShift ell u = ell) ∧
        H.oneClassExtra ell anchor 0 ell (insertShift ell u))
    apply Or.inr
    constructor
    · simp
    · exact ⟨rfl, Or.inr ⟨rfl, u, hEllU, hu, hs, rfl⟩⟩

/-- The local core of the insertion proof. Provided two old
leaves agree up to the defective cut ell but have DIFFERENT
old types at ell+1, inserting the class of anchor gives an
actual role-one meet at precisely ell, without changing
the earlier prefix. This works EVEN when the old meet was
capped at one of the original leaves. -/
theorem insertOneClass_repairs_meet_of_cut_disagreement
    (H : Ordered3Graph Nat) (ell anchor other : Nat)
    (hell : 3 ≤ ell)
    (ha : DiaryLeafPriority.IsLeaf H anchor)
    (hb : DiaryLeafPriority.IsLeaf H other)
    (hlla : ell ≤ anchor) (hllb : ell ≤ other)
    (hsame : H.SameOneTypeBelow ell anchor other)
    (hdiff : ¬ H.SameOneTypeBelow (ell + 1) anchor other) :
    (H.insertOneClass ell anchor).oneMeetLevel
      (insertShift ell anchor) (insertShift ell other) = ell := by
  classical
  let G := H.insertOneClass ell anchor
  let fa := insertShift ell anchor
  let fb := insertShift ell other
  have hRefl : H.SameOneTypeBelow (ell + 1) anchor anchor := by
    intro a b hab hcut
    rfl
  have hPositive : G.edge 0 ell fa :=
    (H.insertOneClass_edge_iff ell anchor anchor hell hlla ha).mpr hRefl
  have hNegative : ¬ G.edge 0 ell fb := by
    intro h
    exact hdiff
      ((H.insertOneClass_edge_iff ell anchor other hell hllb hb).mp h)
  have hTargetPrefix : G.SameOneTypeBelow ell fa fb :=
    (H.insertWithNewEdges_oneTypeBelow_iff ell
      (H.oneClassExtra ell anchor) anchor other).mp hsame
  have hfa : fa = anchor + 1 := by
    simp [fa, insertShift, show ¬ anchor < ell by omega]
  have hfb : fb = other + 1 := by
    simp [fb, insertShift, show ¬ other < ell by omega]
  have hbound : ell ≤ min fa fb := by omega
  have hLower : ell ≤ G.oneMeetLevel fa fb :=
    Nat.le_findGreatest hbound hTargetPrefix
  have hTargetFail : ¬ G.SameOneTypeBelow (ell + 1) fa fb := by
    intro h
    have hEq : G.edge 0 ell fa ↔ G.edge 0 ell fb :=
      h (a := 0) (b := ell) (by omega) (by omega)
    exact hNegative (hEq.mp hPositive)
  have hUpper : G.oneMeetLevel fa fb ≤ ell := by
    by_contra hn
    have hplus : ell + 1 ≤ G.oneMeetLevel fa fb := by omega
    have hSame : G.SameOneTypeBelow (ell + 1) fa fb := by
      intro a b hab hbcut
      exact (G.oneMeetLevel_agree fa fb) hab
        (lt_of_lt_of_le hbcut hplus)
    exact hTargetFail hSame
  exact Nat.le_antisymm hUpper hLower

/-- A defective singleton meet strictly before BOTH leaves
automatically satisfies the old next-level disagreement
hypothesis. Hence it is repaired at the inserted 1-split. -/
theorem insertOneClass_repairs_uncapped_oneMeet
    (H : Ordered3Graph Nat) (ell anchor other : Nat)
    (hell : 3 ≤ ell)
    (ha : DiaryLeafPriority.IsLeaf H anchor)
    (hb : DiaryLeafPriority.IsLeaf H other)
    (hlla : ell < anchor) (hllb : ell < other)
    (hMeet : H.oneMeetLevel anchor other = ell) :
    (H.insertOneClass ell anchor).oneMeetLevel
      (insertShift ell anchor) (insertShift ell other) = ell := by
  classical
  apply H.insertOneClass_repairs_meet_of_cut_disagreement
    ell anchor other hell ha hb hlla.le hllb.le
  · simpa only [hMeet] using H.oneMeetLevel_agree anchor other
  · intro h
    have hbound : ell + 1 ≤ min anchor other := by omega
    have hbad : ell + 1 ≤ H.oneMeetLevel anchor other :=
      Nat.le_findGreatest hbound h
    omega

/-- A Devlin marker witnesses the next-level disagreement when
one leaf sits at the CAPPED meet. This is the needed extra
input from V3 and the non-repeated-edge convention of the
manuscript. The pure ordered-predicate interface intentionally
keeps the diagonal-nonedge assumption explicit. -/
theorem marker_forces_next_oneType_disagreement
    (H : Ordered3Graph Nat) (ell other : Nat)
    (hell : 3 ≤ ell)
    (hMarker :
      (H.edge 1 ell other ∧ ¬ H.edge 1 ell ell) ∨
      (H.edge 2 ell other ∧ ¬ H.edge 2 ell ell)) :
    ¬ H.SameOneTypeBelow (ell + 1) ell other := by
  intro h
  rcases hMarker with ⟨hEdge, hDiagonal⟩ | ⟨hEdge, hDiagonal⟩
  · have hEq : H.edge 1 ell ell ↔ H.edge 1 ell other :=
      h (a := 1) (b := ell) (by omega) (by omega)
    exact hDiagonal (hEq.mpr hEdge)
  · have hEq : H.edge 2 ell ell ↔ H.edge 2 ell other :=
      h (a := 2) (b := ell) (by omega) (by omega)
    exact hDiagonal (hEq.mpr hEdge)

/-- Repair of a capped singleton meet: if the earlier leaf IS
the meet, V3's distinguishing marker supplies the witness
which findGreatest cannot supply past the old cap. -/
theorem insertOneClass_repairs_capped_oneMeet
    (H : Ordered3Graph Nat) (ell other : Nat)
    (hell : 3 ≤ ell)
    (ha : DiaryLeafPriority.IsLeaf H ell)
    (hb : DiaryLeafPriority.IsLeaf H other)
    (hllb : ell < other)
    (hMeet : H.oneMeetLevel ell other = ell)
    (hMarker :
      (H.edge 1 ell other ∧ ¬ H.edge 1 ell ell) ∨
      (H.edge 2 ell other ∧ ¬ H.edge 2 ell ell)) :
    (H.insertOneClass ell ell).oneMeetLevel
      (insertShift ell ell) (insertShift ell other) = ell := by
  apply H.insertOneClass_repairs_meet_of_cut_disagreement
    ell ell other hell ha hb (le_refl ell) hllb.le
  · simpa only [hMeet] using H.oneMeetLevel_agree ell other
  · exact H.marker_forces_next_oneType_disagreement ell other hell hMarker

end Ordered3Graph
end ThreeUniformDiaries
