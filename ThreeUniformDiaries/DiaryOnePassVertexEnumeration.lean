import ThreeUniformDiaries.DiaryOnePassRoleCoverage

/-!
# Canonical vertex enumeration of the one-pass target

The completed indexing of the raw target is not merely locally
finite: it is exactly the disjoint union of ORIGINAL source vertices
and EVENT vertices indexed by original cut m and a Fin index into
the concrete onePassBlock H m.

The forward map assigns each tagged item its actual Nat target level.
The target index-coverage theorem gives surjectivity; the increasing
old-image map, noncollision of old and fresh levels, and cross-block
and within-block event uniqueness give injectivity.

This is a reusable equivalence for subsequent induction over target
levels (V/E/S and type transport). It does not assume S1/S2, claim
the raw target is a diary, or replace its edge relation by an axiom.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Original vertices or genuinely indexed finite-block events. -/
abbrev OnePassTaggedVertex (H : Ordered3Graph Nat) : Type :=
  Nat ⊕ (Σ m : Nat, Fin (onePassBlock H m).length)

/-- The actual target natural-number level of a tagged vertex. -/
noncomputable def onePassTaggedIndex
    (H : Ordered3Graph Nat) : OnePassTaggedVertex H → Nat
  | Sum.inl m => onePassOldImage H m
  | Sum.inr ⟨m, i⟩ => onePassEventPosition H m i

/-- No two different original/event tags denote the same target
natural-number level. -/
theorem onePassTaggedIndex_injective
    (H : Ordered3Graph Nat) :
    Function.Injective (onePassTaggedIndex H) := by
  intro x y hxy
  cases x with
  | inl m =>
      cases y with
      | inl n =>
          change onePassOldImage H m = onePassOldImage H n at hxy
          have hmn : m = n :=
            (onePassOldImage_strictMono H).injective hxy
          subst n
          rfl
      | inr q =>
          obtain ⟨n, j⟩ := q
          change onePassOldImage H m =
            onePassEventPosition H n j at hxy
          exact False.elim
            ((onePassEventPosition_ne_oldImage H n j m) hxy.symm)
  | inr p =>
      cases y with
      | inl n =>
          obtain ⟨m, i⟩ := p
          change onePassEventPosition H m i =
            onePassOldImage H n at hxy
          exact False.elim
            ((onePassEventPosition_ne_oldImage H m i n) hxy)
      | inr q =>
          obtain ⟨m, i⟩ := p
          obtain ⟨n, j⟩ := q
          change onePassEventPosition H m i =
            onePassEventPosition H n j at hxy
          have hmn : m = n :=
            onePassEventPosition_eq_cut H m n i j hxy
          subst n
          have hij : i = j :=
            onePassEventPosition_injective_same_cut H m i j hxy
          subst j
          rfl

/-- There are no omitted target natural-number levels. -/
theorem onePassTaggedIndex_surjective
    (H : Ordered3Graph Nat) :
    Function.Surjective (onePassTaggedIndex H) := by
  intro z
  rcases onePass_target_index_covered H z with
      ⟨m, hm⟩ | ⟨m, i, hi⟩
  · exact ⟨Sum.inl m, hm⟩
  · exact ⟨Sum.inr ⟨m, i⟩, hi⟩

theorem onePassTaggedIndex_bijective
    (H : Ordered3Graph Nat) :
    Function.Bijective (onePassTaggedIndex H) :=
  ⟨onePassTaggedIndex_injective H,
    onePassTaggedIndex_surjective H⟩

/-- Every natural-number target vertex has one and only one
concrete old-or-event description. -/
noncomputable def onePassVertexEquiv
    (H : Ordered3Graph Nat) : OnePassTaggedVertex H ≃ Nat :=
  Equiv.ofBijective (onePassTaggedIndex H)
    (onePassTaggedIndex_bijective H)

end DiaryLeafPriority
end ThreeUniformDiaries
