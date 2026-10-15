import ThreeUniformDiaries.AuxTypes

/-!
# The safe insertion step in pre-diary completion

The manuscript inserts a new vertex at a defective meet level ell,
shifting each old vertex t >= ell to t+1 and adding fresh edges
incident with the new vertex. Two properties must be verified
BEFORE examining the specific 1-/2-split edge construction:

* the shifted old hypergraph remains a genuinely induced copy,
  including reflection of old nonedges;
* all singleton and auxiliary pair-type agreements over the
  protected initial cut ell remain exactly unchanged.

We prove these for ARBITRARY new edges incident with ell.
Nothing in this module claims that the insertion establishes
a V/E/S pre-diary, preserves meets at or above ell, or
terminates the completion procedure. Those are separate,
substantive obligations.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Rename all old levels at or after ell by adding one. -/
def insertShift (ell t : Nat) : Nat :=
  if t < ell then t else t + 1

/-- The inverse renaming, only used away from the inserted vertex.
At ell its value is arbitrary and is excluded from old edges. -/
def eraseInserted (ell t : Nat) : Nat :=
  if t < ell then t else t - 1

theorem insertShift_strictMono (ell : Nat) :
    StrictMono (insertShift ell) := by
  intro a b hab
  unfold insertShift
  by_cases ha : a < ell <;>
    by_cases hb : b < ell <;>
    simp [ha, hb] <;> omega

theorem insertShift_before (ell t : Nat) (ht : t < ell) :
    insertShift ell t = t := by
  simp [insertShift, ht]

theorem insertShift_ne (ell t : Nat) :
    insertShift ell t ≠ ell := by
  unfold insertShift
  by_cases ht : t < ell <;> simp [ht] <;> omega

theorem eraseInserted_insertShift (ell t : Nat) :
    eraseInserted ell (insertShift ell t) = t := by
  unfold insertShift eraseInserted
  by_cases ht : t < ell
  · simp [ht]
  · have hnot : ¬ t + 1 < ell := by omega
    simp [ht, hnot]

/-- The old edges are renamed and no old edge meets ell. -/
def isolatedInsert (H : Ordered3Graph Nat) (ell : Nat) :
    Ordered3Graph Nat where
  edge x y z :=
    x ≠ ell ∧ y ≠ ell ∧ z ≠ ell ∧
      H.edge (eraseInserted ell x)
        (eraseInserted ell y) (eraseInserted ell z)

theorem isolatedInsert_edge_iff_image
    (H : Ordered3Graph Nat) (ell a b c : Nat) :
    (isolatedInsert H ell).edge
      (insertShift ell a) (insertShift ell b)
      (insertShift ell c) ↔ H.edge a b c := by
  simp [isolatedInsert, insertShift_ne, eraseInserted_insertShift]

/-- Any additional edges must contain the new vertex ell.
This restriction is sufficient for preserving the old induced
copy but not for preserving all old type meets against ell. -/
def insertWithNewEdges
    (H : Ordered3Graph Nat) (ell : Nat)
    (extra : Nat → Nat → Nat → Prop) :
    Ordered3Graph Nat where
  edge x y z :=
    (isolatedInsert H ell).edge x y z ∨
      ((x = ell ∨ y = ell ∨ z = ell) ∧ extra x y z)

theorem insertWithNewEdges_edge_iff_image
    (H : Ordered3Graph Nat) (ell : Nat)
    (extra : Nat → Nat → Nat → Prop)
    (a b c : Nat) :
    (insertWithNewEdges H ell extra).edge
      (insertShift ell a) (insertShift ell b)
      (insertShift ell c) ↔ H.edge a b c := by
  simp [insertWithNewEdges, isolatedInsert,
    insertShift_ne, eraseInserted_insertShift]

/-- The old hypergraph is an induced, order-preserving
substructure after inserting the fresh level. -/
noncomputable def embedding_insertWithNewEdges
    (H : Ordered3Graph Nat) (ell : Nat)
    (extra : Nat → Nat → Nat → Prop) :
    Embedding H (insertWithNewEdges H ell extra) where
  toFun := insertShift ell
  strictMono := insertShift_strictMono ell
  edge_iff := by
    intro a b c hab hbc
    exact (insertWithNewEdges_edge_iff_image
      H ell extra a b c).symm

/-- Exactly preserve singleton-type agreement through the
old protected cut ell, even after arbitrary new edges at ell. -/
theorem insertWithNewEdges_oneTypeBelow_iff
    (H : Ordered3Graph Nat) (ell : Nat)
    (extra : Nat → Nat → Nat → Prop)
    (u v : Nat) :
    H.SameOneTypeBelow ell u v ↔
      (insertWithNewEdges H ell extra).SameOneTypeBelow ell
        (insertShift ell u) (insertShift ell v) := by
  constructor
  · intro hs x y hxy hy
    have hx : x < ell := lt_trans hxy hy
    have heU : H.edge x y u ↔
        (insertWithNewEdges H ell extra).edge
          x y (insertShift ell u) := by
      simpa only [insertShift_before ell x hx,
        insertShift_before ell y hy] using
        (insertWithNewEdges_edge_iff_image
          H ell extra x y u).symm
    have heV : H.edge x y v ↔
        (insertWithNewEdges H ell extra).edge
          x y (insertShift ell v) := by
      simpa only [insertShift_before ell x hx,
        insertShift_before ell y hy] using
        (insertWithNewEdges_edge_iff_image
          H ell extra x y v).symm
    exact heU.symm.trans ((hs hxy hy).trans heV)
  · intro ht x y hxy hy
    have hx : x < ell := lt_trans hxy hy
    have heU : H.edge x y u ↔
        (insertWithNewEdges H ell extra).edge
          x y (insertShift ell u) := by
      simpa only [insertShift_before ell x hx,
        insertShift_before ell y hy] using
        (insertWithNewEdges_edge_iff_image
          H ell extra x y u).symm
    have heV : H.edge x y v ↔
        (insertWithNewEdges H ell extra).edge
          x y (insertShift ell v) := by
      simpa only [insertShift_before ell x hx,
        insertShift_before ell y hy] using
        (insertWithNewEdges_edge_iff_image
          H ell extra x y v).symm
    exact heU.trans ((ht hxy hy).trans heV.symm)

/-- Exactly preserve auxiliary pair-type agreement through ell.
The fresh vertex is at ell and hence is not tested below ell. -/
theorem insertWithNewEdges_auxTypeBelow_iff
    (H : Ordered3Graph Nat) (ell : Nat)
    (extra : Nat → Nat → Nat → Prop)
    (u₀ u₁ v₀ v₁ : Nat) :
    H.SameAuxTypeBelow ell u₀ u₁ v₀ v₁ ↔
      (insertWithNewEdges H ell extra).SameAuxTypeBelow ell
        (insertShift ell u₀) (insertShift ell u₁)
        (insertShift ell v₀) (insertShift ell v₁) := by
  constructor
  · intro hs x hx
    have heU : H.edge x u₀ u₁ ↔
        (insertWithNewEdges H ell extra).edge
          x (insertShift ell u₀) (insertShift ell u₁) := by
      simpa only [insertShift_before ell x hx] using
        (insertWithNewEdges_edge_iff_image
          H ell extra x u₀ u₁).symm
    have heV : H.edge x v₀ v₁ ↔
        (insertWithNewEdges H ell extra).edge
          x (insertShift ell v₀) (insertShift ell v₁) := by
      simpa only [insertShift_before ell x hx] using
        (insertWithNewEdges_edge_iff_image
          H ell extra x v₀ v₁).symm
    exact heU.symm.trans ((hs hx).trans heV)
  · intro ht x hx
    have heU : H.edge x u₀ u₁ ↔
        (insertWithNewEdges H ell extra).edge
          x (insertShift ell u₀) (insertShift ell u₁) := by
      simpa only [insertShift_before ell x hx] using
        (insertWithNewEdges_edge_iff_image
          H ell extra x u₀ u₁).symm
    have heV : H.edge x v₀ v₁ ↔
        (insertWithNewEdges H ell extra).edge
          x (insertShift ell v₀) (insertShift ell v₁) := by
      simpa only [insertShift_before ell x hx] using
        (insertWithNewEdges_edge_iff_image
          H ell extra x v₀ v₁).symm
    exact heU.trans ((ht hx).trans heV.symm)

/-- Consequently the full ordered-pair type at the protected
cut is preserved, with all three components. -/
theorem insertWithNewEdges_twoTypeBelow_iff
    (H : Ordered3Graph Nat) (ell : Nat)
    (extra : Nat → Nat → Nat → Prop)
    (u₀ u₁ v₀ v₁ : Nat) :
    H.SameTwoTypeBelow ell u₀ u₁ v₀ v₁ ↔
      (insertWithNewEdges H ell extra).SameTwoTypeBelow ell
        (insertShift ell u₀) (insertShift ell u₁)
        (insertShift ell v₀) (insertShift ell v₁) := by
  change
    (H.SameOneTypeBelow ell u₀ v₀ ∧
     H.SameOneTypeBelow ell u₁ v₁ ∧
     H.SameAuxTypeBelow ell u₀ u₁ v₀ v₁) ↔
    ((insertWithNewEdges H ell extra).SameOneTypeBelow ell
       (insertShift ell u₀) (insertShift ell v₀) ∧
     (insertWithNewEdges H ell extra).SameOneTypeBelow ell
       (insertShift ell u₁) (insertShift ell v₁) ∧
     (insertWithNewEdges H ell extra).SameAuxTypeBelow ell
       (insertShift ell u₀) (insertShift ell u₁)
       (insertShift ell v₀) (insertShift ell v₁))
  rw [insertWithNewEdges_oneTypeBelow_iff H ell extra u₀ v₀,
      insertWithNewEdges_oneTypeBelow_iff H ell extra u₁ v₁,
      insertWithNewEdges_auxTypeBelow_iff
        H ell extra u₀ u₁ v₀ v₁]

end Ordered3Graph
end ThreeUniformDiaries
