import ThreeUniformDiaries.DiaryPrediaryInsertionInvariant

/-!
# Exact type-agreement transport through an inserted diary level

Earlier insertion lemmas preserve the old induced graph and
type tests STRICTLY BELOW the inserted cut ell. For V1/V2
coherence at old splits shifted PAST ell one needs a
stronger transport statement.

Every old node occurs at its shifted image. The only new
singleton tests (x,y,shift u) to consider have x=ell or
y=ell; the only new auxiliary tests (x,shift u,shift v)
have x=ell. If those newly inserted tests agree for the
old types under comparison, all old type-agreement
through m transfers to the shifted cut shift(m).

These are conditional but fully general transport lemmas:
concrete 1-/2-class insertions will discharge the listed
fresh-test hypotheses. No pre-diary or meet hypothesis is
assumed here.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Away from the new vertex ell the deletion and insertion
maps are mutually inverse. -/
theorem insertShift_eraseInserted_of_ne
    (ell x : Nat) (hx : x ≠ ell) :
    insertShift ell (eraseInserted ell x) = x := by
  unfold insertShift eraseInserted
  by_cases hlt : x < ell
  · simp [hlt]
  · have hgt : ell < x := by omega
    have hnot : ¬ x - 1 < ell := by omega
    simp [hlt, hnot]
    omega

/-- Deletion is strictly increasing on the old vertex set. -/
theorem eraseInserted_lt_of_not_new
    (ell x y : Nat) (hxy : x < y)
    (hx : x ≠ ell) (hy : y ≠ ell) :
    eraseInserted ell x < eraseInserted ell y := by
  unfold eraseInserted
  split_ifs <;> omega

/-- Every old vertex before the shifted cut m comes
from an old source vertex strictly before m. -/
theorem eraseInserted_lt_of_lt_shift
    (ell m x : Nat)
    (hx : x ≠ ell) (hxm : x < insertShift ell m) :
    eraseInserted ell x < m := by
  unfold eraseInserted insertShift at *
  split_ifs at * <;> omega

/-- When all FRESH singleton tests agree, an arbitrary
old singleton type agreement through m is preserved
at the shifted cut. This is the exact bridge needed for
coherence of shifted old 1-splits. -/
theorem oneTypeBelow_shift_of_fresh_agreement
    (H : Ordered3Graph Nat)
    (ell m u v : Nat)
    (extra : Nat → Nat → Nat → Prop)
    (hOld : H.SameOneTypeBelow m u v)
    (hFresh :
      ∀ x y, x < y → y < insertShift ell m →
        (x = ell ∨ y = ell) →
        ((H.insertWithNewEdges ell extra).edge x y
            (insertShift ell u) ↔
         (H.insertWithNewEdges ell extra).edge x y
            (insertShift ell v))) :
    (H.insertWithNewEdges ell extra).SameOneTypeBelow
      (insertShift ell m) (insertShift ell u) (insertShift ell v) := by
  intro x y hxy hym
  by_cases hx : x = ell
  · exact hFresh x y hxy hym (Or.inl hx)
  by_cases hy : y = ell
  · exact hFresh x y hxy hym (Or.inr hy)
  have hxyOld : eraseInserted ell x < eraseInserted ell y :=
    eraseInserted_lt_of_not_new ell x y hxy hx hy
  have hyOld : eraseInserted ell y < m :=
    eraseInserted_lt_of_lt_shift ell m y hy hym
  have hCmp := hOld hxyOld hyOld
  have ex : insertShift ell (eraseInserted ell x) = x :=
    insertShift_eraseInserted_of_ne ell x hx
  have ey : insertShift ell (eraseInserted ell y) = y :=
    insertShift_eraseInserted_of_ne ell y hy
  calc
    (H.insertWithNewEdges ell extra).edge x y (insertShift ell u) ↔
      H.edge (eraseInserted ell x) (eraseInserted ell y) u := by
        rw [← ex, ← ey]
        exact (H.insertWithNewEdges_edge_iff_image ell extra
          (eraseInserted ell x) (eraseInserted ell y) u)
    _ ↔ H.edge (eraseInserted ell x) (eraseInserted ell y) v := hCmp
    _ ↔ (H.insertWithNewEdges ell extra).edge x y
          (insertShift ell v) := by
        rw [← ex, ← ey]
        exact (H.insertWithNewEdges_edge_iff_image ell extra
          (eraseInserted ell x) (eraseInserted ell y) v).symm

/-- Auxiliary pair agreement is transported through a shift
if the ONE new auxiliary-coordinate test at ell agrees. -/
theorem auxTypeBelow_shift_of_fresh_agreement
    (H : Ordered3Graph Nat)
    (ell m u₀ u₁ v₀ v₁ : Nat)
    (extra : Nat → Nat → Nat → Prop)
    (hOld : H.SameAuxTypeBelow m u₀ u₁ v₀ v₁)
    (hFresh :
      (H.insertWithNewEdges ell extra).edge ell
          (insertShift ell u₀) (insertShift ell u₁) ↔
      (H.insertWithNewEdges ell extra).edge ell
          (insertShift ell v₀) (insertShift ell v₁)) :
    (H.insertWithNewEdges ell extra).SameAuxTypeBelow
      (insertShift ell m)
      (insertShift ell u₀) (insertShift ell u₁)
      (insertShift ell v₀) (insertShift ell v₁) := by
  intro x hxm
  by_cases hx : x = ell
  · subst x
    exact hFresh
  have hxOld : eraseInserted ell x < m :=
    eraseInserted_lt_of_lt_shift ell m x hx hxm
  have hCmp := hOld hxOld
  have ex : insertShift ell (eraseInserted ell x) = x :=
    insertShift_eraseInserted_of_ne ell x hx
  calc
    (H.insertWithNewEdges ell extra).edge x
       (insertShift ell u₀) (insertShift ell u₁) ↔
      H.edge (eraseInserted ell x) u₀ u₁ := by
        rw [← ex]
        exact (H.insertWithNewEdges_edge_iff_image ell extra
          (eraseInserted ell x) u₀ u₁)
    _ ↔ H.edge (eraseInserted ell x) v₀ v₁ := hCmp
    _ ↔ (H.insertWithNewEdges ell extra).edge x
          (insertShift ell v₀) (insertShift ell v₁) := by
        rw [← ex]
        exact (H.insertWithNewEdges_edge_iff_image ell extra
          (eraseInserted ell x) v₀ v₁).symm

/-- The full ordered-pair type is transported by two
fresh singleton tests and one fresh auxiliary test. -/
theorem twoTypeBelow_shift_of_fresh_agreement
    (H : Ordered3Graph Nat)
    (ell m u₀ u₁ v₀ v₁ : Nat)
    (extra : Nat → Nat → Nat → Prop)
    (hOld : H.SameTwoTypeBelow m u₀ u₁ v₀ v₁)
    (hFresh0 :
      ∀ x y, x < y → y < insertShift ell m →
        (x = ell ∨ y = ell) →
        ((H.insertWithNewEdges ell extra).edge x y
            (insertShift ell u₀) ↔
         (H.insertWithNewEdges ell extra).edge x y
            (insertShift ell v₀)))
    (hFresh1 :
      ∀ x y, x < y → y < insertShift ell m →
        (x = ell ∨ y = ell) →
        ((H.insertWithNewEdges ell extra).edge x y
            (insertShift ell u₁) ↔
         (H.insertWithNewEdges ell extra).edge x y
            (insertShift ell v₁)))
    (hFreshAux :
      (H.insertWithNewEdges ell extra).edge ell
          (insertShift ell u₀) (insertShift ell u₁) ↔
      (H.insertWithNewEdges ell extra).edge ell
          (insertShift ell v₀) (insertShift ell v₁)) :
    (H.insertWithNewEdges ell extra).SameTwoTypeBelow
      (insertShift ell m)
      (insertShift ell u₀) (insertShift ell u₁)
      (insertShift ell v₀) (insertShift ell v₁) := by
  rcases hOld with ⟨h0, h1, hAux⟩
  exact ⟨H.oneTypeBelow_shift_of_fresh_agreement
            ell m u₀ v₀ extra h0 hFresh0,
         H.oneTypeBelow_shift_of_fresh_agreement
            ell m u₁ v₁ extra h1 hFresh1,
         H.auxTypeBelow_shift_of_fresh_agreement
            ell m u₀ u₁ v₀ v₁ extra hAux hFreshAux⟩

end Ordered3Graph
end ThreeUniformDiaries
