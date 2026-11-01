import ThreeUniformDiaries.DiaryLeafGeneratedStageCompatibility

/-!
# Relative diary successors require target vertices of the correct role

A positive numerical gap between the fixed old support images may
contain no vertex of the diary role required by a new supported
source split. This gives a further necessary condition independent
of the raw number of unused target indices.

Every valid relative successor preserving old selected leaf images
therefore supplies a target one-split or two-split between the old
fixed images whenever the new support includes a source vertex of
that role in the corresponding source interval.

These statements are purely conditional obstructions. In particular,
no concrete generic target diary with a missing role slot is
constructed here. A new-leaf realization theorem must establish
role-appropriate slots as well as the previously checked order
reserve, mixed old-pair edges, and numerical meets.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace AdmissibleCofinalDiaryStage

variable {H K : Ordered3Graph Nat} {F : Nat → Nat}
variable {m : Nat} {f g : Nat → Nat}

/-- A new supported source vertex between two OLD supported
vertices must be placed between their fixed old target images,
regardless of the diary role of that new vertex. -/
theorem successor_inserted_vertex_interval
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (Q : AdmissibleCofinalDiaryStage H K F (m + 1) g)
    (hKeep : ∀ u : Nat, u ∈ countableDiaryLeafPrefix H m →
      g u = f u)
    {x y s : Nat}
    (hx : x ∈ countableDiaryFiniteSupport H m)
    (hy : y ∈ countableDiaryFiniteSupport H m)
    (hs : s ∈ countableDiaryFiniteSupport H (m + 1))
    (hxs : x < s) (hsy : s < y) :
    f x < g s ∧ g s < f y := by
  have hCompat : CofinalDiaryStageCompatible H m f g :=
    P.successor_compatible_of_selected_leaf_agreement Q hKeep
  have hxNew : x ∈ countableDiaryFiniteSupport H (m + 1) :=
    (countableDiaryFiniteSupport_mono H m (m + 1) (by omega)) hx
  have hyNew : y ∈ countableDiaryFiniteSupport H (m + 1) :=
    (countableDiaryFiniteSupport_mono H m (m + 1) (by omega)) hy
  have hLeft : g x < g s := Q.ordered x s hxNew hs hxs
  have hRight : g s < g y := Q.ordered s y hs hyNew hsy
  rw [hCompat x hx] at hLeft
  rw [hCompat y hy] at hRight
  exact ⟨hLeft,hRight⟩

/-- An inserted actual source one-split forces a target one-split
in the open interval between the two fixed old target images. -/
theorem successor_requires_oneSplit_slot
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (Q : AdmissibleCofinalDiaryStage H K F (m + 1) g)
    (hKeep : ∀ u : Nat, u ∈ countableDiaryLeafPrefix H m →
      g u = f u)
    {x y s : Nat}
    (hx : x ∈ countableDiaryFiniteSupport H m)
    (hy : y ∈ countableDiaryFiniteSupport H m)
    (hs : s ∈ countableDiaryFiniteSupport H (m + 1))
    (hxs : x < s) (hsy : s < y)
    (hRole : IsOneSplit H s) :
    ∃ t : Nat, f x < t ∧ t < f y ∧ IsOneSplit K t := by
  obtain ⟨hLeft,hRight⟩ :=
    P.successor_inserted_vertex_interval Q hKeep hx hy hs hxs hsy
  exact ⟨g s,hLeft,hRight,Q.one_split_role s hs hRole⟩

/-- An inserted actual source two-split forces a target two-split
between the fixed old images, not merely a spare target index. -/
theorem successor_requires_twoSplit_slot
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (Q : AdmissibleCofinalDiaryStage H K F (m + 1) g)
    (hKeep : ∀ u : Nat, u ∈ countableDiaryLeafPrefix H m →
      g u = f u)
    {x y s : Nat}
    (hx : x ∈ countableDiaryFiniteSupport H m)
    (hy : y ∈ countableDiaryFiniteSupport H m)
    (hs : s ∈ countableDiaryFiniteSupport H (m + 1))
    (hxs : x < s) (hsy : s < y)
    (hRole : IsTwoSplit H s) :
    ∃ t : Nat, f x < t ∧ t < f y ∧ IsTwoSplit K t := by
  obtain ⟨hLeft,hRight⟩ :=
    P.successor_inserted_vertex_interval Q hKeep hx hy hs hxs hsy
  exact ⟨g s,hLeft,hRight,Q.two_split_role s hs hRole⟩

/-- A literal lack of target one-splits in the required interval
certifies that no leaf-image-preserving relative successor exists. -/
theorem no_successor_of_missing_oneSplit_slot
    (P : AdmissibleCofinalDiaryStage H K F m f)
    {x y s : Nat}
    (hx : x ∈ countableDiaryFiniteSupport H m)
    (hy : y ∈ countableDiaryFiniteSupport H m)
    (hs : s ∈ countableDiaryFiniteSupport H (m + 1))
    (hxs : x < s) (hsy : s < y)
    (hRole : IsOneSplit H s)
    (hNo : ∀ t : Nat, f x < t → t < f y → ¬ IsOneSplit K t) :
    ¬ ∃ g : Nat → Nat,
      AdmissibleCofinalDiaryStage H K F (m + 1) g ∧
      (∀ u : Nat, u ∈ countableDiaryLeafPrefix H m →
        g u = f u) := by
  rintro ⟨g,Q,hKeep⟩
  obtain ⟨t,hLeft,hRight,hRoleTarget⟩ :=
    P.successor_requires_oneSplit_slot Q hKeep hx hy hs hxs hsy hRole
  exact (hNo t hLeft hRight) hRoleTarget

/-- The analogous independent role-slot obstruction for
a new source two-split. -/
theorem no_successor_of_missing_twoSplit_slot
    (P : AdmissibleCofinalDiaryStage H K F m f)
    {x y s : Nat}
    (hx : x ∈ countableDiaryFiniteSupport H m)
    (hy : y ∈ countableDiaryFiniteSupport H m)
    (hs : s ∈ countableDiaryFiniteSupport H (m + 1))
    (hxs : x < s) (hsy : s < y)
    (hRole : IsTwoSplit H s)
    (hNo : ∀ t : Nat, f x < t → t < f y → ¬ IsTwoSplit K t) :
    ¬ ∃ g : Nat → Nat,
      AdmissibleCofinalDiaryStage H K F (m + 1) g ∧
      (∀ u : Nat, u ∈ countableDiaryLeafPrefix H m →
        g u = f u) := by
  rintro ⟨g,Q,hKeep⟩
  obtain ⟨t,hLeft,hRight,hRoleTarget⟩ :=
    P.successor_requires_twoSplit_slot Q hKeep hx hy hs hxs hsy hRole
  exact (hNo t hLeft hRight) hRoleTarget

end AdmissibleCofinalDiaryStage
end DiaryLeafPriority
end ThreeUniformDiaries
