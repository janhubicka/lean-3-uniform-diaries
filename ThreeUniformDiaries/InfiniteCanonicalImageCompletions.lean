import ThreeUniformDiaries.InfiniteGeometricImageMeetClosed
import ThreeUniformDiaries.RelativeStrongAmbientTransitivity

/-!
# Actual E1 and E0 image completions INSIDE the outer strong coordinate

For two synchronized triples of genuine strong pictures with inner level
map sigma and outer level map f, the pointwise canonical image of each
inner E1/E0 coordinate picture is meet-closed and lies in the outer
coordinate picture.

The protected relative construction completes these images inside
the respective outer pictures. Both resulting completed pictures are
genuine AMBIENT infinite strong pictures with selected map f ∘ sigma
and with root equal to the actual image of the inner root.

This does not assert that their canonical maps equal the composites;
that will follow from the separate E1/E0 cone and uniqueness theorems.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem exists_infiniteOne_image_completion_with_subset
    {S₁ S₂ U₁ U₂ : Set CoordNode} {sigma f : Nat → Nat}
    {rS₁ : OneNode (sigma 0)} {rS₂ : AuxNode (sigma 0)}
    {rU₁ : OneNode (f 0)} {rU₂ : AuxNode (f 0)}
    (hS₁ : InfiniteStrongPicture S₁ sigma (.one (sigma 0) rS₁))
    (hS₂ : InfiniteStrongPicture S₂ sigma (.aux (sigma 0) rS₂))
    (hU₁ : InfiniteStrongPicture U₁ f (.one (f 0) rU₁))
    (hU₂ : InfiniteStrongPicture U₂ f (.aux (f 0) rU₂))
    (hsigma : StrictMono sigma) (hf : StrictMono f) :
    ∃ (V₁ : Set CoordNode),
      ∃ hV₁ : InfiniteStrongPicture V₁ (fun i => f (sigma i))
        (.one (f (sigma 0))
          (infiniteOneCanonicalMap hU₁ hU₂ (sigma 0) rS₁).val),
        V₁ ⊆ U₁ ∧ infiniteOneImage hU₁ hU₂ S₁ ⊆ V₁ := by
  let E : Set CoordNode := infiniteOneImage hU₁ hU₂ S₁
  let r : CoordNode :=
    .one (f (sigma 0))
      (infiniteOneCanonicalMap hU₁ hU₂ (sigma 0) rS₁).val
  have hEU : E ⊆ U₁ := infiniteOneImage_subset hU₁ hU₂ S₁
  have hE : MeetClosed E :=
    infiniteOneImage_meetClosed hU₁ hU₂ hf S₁ hS₁.meet_closed
  have hlevels : ∀ x ∈ E, ∃ i : Nat, level x = f (sigma i) := by
    intro x hx
    rcases hx with ⟨n, a, ha, rfl⟩
    obtain ⟨i, hi⟩ := hS₁.selected_levels (.one n a) ha
    refine ⟨i, ?_⟩
    change f n = f (sigma i)
    change n = sigma i at hi
    rw [hi]
  have hrU : r ∈ U₁ :=
    (infiniteOneCanonicalMap hU₁ hU₂ (sigma 0) rS₁).property
  have hrLevel : level r = f (sigma 0) := rfl
  have hrootLevel : level (CoordNode.one (f 0) rU₁) = f 0 := rfl
  have hrBelow : ∀ x ∈ E, r ≤ x := by
    intro x hx
    rcases hx with ⟨n, a, ha, rfl⟩
    have hroot := hS₁.root_le (.one n a) ha
    have hcut : a.truncate (sigma 0) = rS₁ := by
      have heq := hroot.2
      change CoordNode.one (sigma 0) (a.truncate (sigma 0)) =
        CoordNode.one (sigma 0) rS₁ at heq
      injection heq
    have htr := infiniteOneCanonicalMap_truncate hU₁ hU₂ hf
      (sigma 0) n hroot.1 a
    rw [hcut] at htr
    refine ⟨hf.monotone hroot.1, ?_⟩
    change CoordNode.one (f (sigma 0))
      ((infiniteOneCanonicalMap hU₁ hU₂ n a).val.truncate (f (sigma 0))) =
      CoordNode.one (f (sigma 0))
        (infiniteOneCanonicalMap hU₁ hU₂ (sigma 0) rS₁).val
    exact congrArg (CoordNode.one (f (sigma 0))) htr
  obtain ⟨V₁, hEV, hRelative⟩ :=
    exists_relative_infinite_strong_completion
      hU₁ hf hrootLevel E hE hEU sigma hsigma hlevels
      r hrU hrLevel hrBelow
  have hV₁ : InfiniteStrongPicture V₁ (fun i => f (sigma i)) r :=
    relativeInfiniteStrongPicture_to_ambient hU₁ hf hsigma hRelative
  exact ⟨V₁, hV₁, hRelative.subset_U, hEV⟩

theorem exists_infiniteEnum_image_completion_with_subset
    {S₀ S₁ S₂ U₀ U₁ U₂ : Set CoordNode} {sigma f : Nat → Nat}
    {rS₀ : EnumNode (sigma 0)} {rS₁ : OneNode (sigma 0)}
    {rS₂ : AuxNode (sigma 0)}
    {rU₀ : EnumNode (f 0)} {rU₁ : OneNode (f 0)}
    {rU₂ : AuxNode (f 0)}
    (hS₀ : InfiniteStrongPicture S₀ sigma (.enum (sigma 0) rS₀))
    (hS₁ : InfiniteStrongPicture S₁ sigma (.one (sigma 0) rS₁))
    (hS₂ : InfiniteStrongPicture S₂ sigma (.aux (sigma 0) rS₂))
    (hU₀ : InfiniteStrongPicture U₀ f (.enum (f 0) rU₀))
    (hU₁ : InfiniteStrongPicture U₁ f (.one (f 0) rU₁))
    (hU₂ : InfiniteStrongPicture U₂ f (.aux (f 0) rU₂))
    (hsigma : StrictMono sigma) (hf : StrictMono f) :
    ∃ (V₀ : Set CoordNode),
      ∃ hV₀ : InfiniteStrongPicture V₀ (fun i => f (sigma i))
        (.enum (f (sigma 0))
          (infiniteEnumCanonicalMap hU₀ hU₁ hU₂ (sigma 0) rS₀).val),
        V₀ ⊆ U₀ ∧ infiniteEnumImage hU₀ hU₁ hU₂ S₀ ⊆ V₀ := by
  let E : Set CoordNode := infiniteEnumImage hU₀ hU₁ hU₂ S₀
  let r : CoordNode :=
    .enum (f (sigma 0))
      (infiniteEnumCanonicalMap hU₀ hU₁ hU₂ (sigma 0) rS₀).val
  have hEU : E ⊆ U₀ := infiniteEnumImage_subset hU₀ hU₁ hU₂ S₀
  have hE : MeetClosed E :=
    infiniteEnumImage_meetClosed hU₀ hU₁ hU₂ hf S₀ hS₀.meet_closed
  have hlevels : ∀ x ∈ E, ∃ i : Nat, level x = f (sigma i) := by
    intro x hx
    rcases hx with ⟨n, a, ha, rfl⟩
    obtain ⟨i, hi⟩ := hS₀.selected_levels (.enum n a) ha
    refine ⟨i, ?_⟩
    change f n = f (sigma i)
    change n = sigma i at hi
    rw [hi]
  have hrU : r ∈ U₀ :=
    (infiniteEnumCanonicalMap hU₀ hU₁ hU₂ (sigma 0) rS₀).property
  have hrLevel : level r = f (sigma 0) := rfl
  have hrootLevel : level (CoordNode.enum (f 0) rU₀) = f 0 := rfl
  have hrBelow : ∀ x ∈ E, r ≤ x := by
    intro x hx
    rcases hx with ⟨n, a, ha, rfl⟩
    have hroot := hS₀.root_le (.enum n a) ha
    have hcut : a.truncate (sigma 0) = rS₀ := by
      have heq := hroot.2
      change CoordNode.enum (sigma 0) (a.truncate (sigma 0)) =
        CoordNode.enum (sigma 0) rS₀ at heq
      injection heq
    have htr := infiniteEnumCanonicalMap_truncate hU₀ hU₁ hU₂ hf
      (sigma 0) n hroot.1 a
    rw [hcut] at htr
    refine ⟨hf.monotone hroot.1, ?_⟩
    change CoordNode.enum (f (sigma 0))
      ((infiniteEnumCanonicalMap hU₀ hU₁ hU₂ n a).val.truncate (f (sigma 0))) =
      CoordNode.enum (f (sigma 0))
        (infiniteEnumCanonicalMap hU₀ hU₁ hU₂ (sigma 0) rS₀).val
    exact congrArg (CoordNode.enum (f (sigma 0))) htr
  obtain ⟨V₀, hEV, hRelative⟩ :=
    exists_relative_infinite_strong_completion
      hU₀ hf hrootLevel E hE hEU sigma hsigma hlevels
      r hrU hrLevel hrBelow
  have hV₀ : InfiniteStrongPicture V₀ (fun i => f (sigma i)) r :=
    relativeInfiniteStrongPicture_to_ambient hU₀ hf hsigma hRelative
  exact ⟨V₀, hV₀, hRelative.subset_U, hEV⟩


theorem exists_infiniteOne_image_completion
    {S₁ S₂ U₁ U₂ : Set CoordNode} {sigma f : Nat → Nat}
    {rS₁ : OneNode (sigma 0)} {rS₂ : AuxNode (sigma 0)}
    {rU₁ : OneNode (f 0)} {rU₂ : AuxNode (f 0)}
    (hS₁ : InfiniteStrongPicture S₁ sigma (.one (sigma 0) rS₁))
    (hS₂ : InfiniteStrongPicture S₂ sigma (.aux (sigma 0) rS₂))
    (hU₁ : InfiniteStrongPicture U₁ f (.one (f 0) rU₁))
    (hU₂ : InfiniteStrongPicture U₂ f (.aux (f 0) rU₂))
    (hsigma : StrictMono sigma) (hf : StrictMono f) :
    ∃ (V₁ : Set CoordNode),
      ∃ hV₁ : InfiniteStrongPicture V₁ (fun i => f (sigma i))
        (.one (f (sigma 0))
          (infiniteOneCanonicalMap hU₁ hU₂ (sigma 0) rS₁).val),
        infiniteOneImage hU₁ hU₂ S₁ ⊆ V₁ := by
  obtain ⟨V, hV, _, hE⟩ :=
    exists_infiniteOne_image_completion_with_subset
      hS₁ hS₂ hU₁ hU₂ hsigma hf
  exact ⟨V, hV, hE⟩

theorem exists_infiniteEnum_image_completion
    {S₀ S₁ S₂ U₀ U₁ U₂ : Set CoordNode} {sigma f : Nat → Nat}
    {rS₀ : EnumNode (sigma 0)} {rS₁ : OneNode (sigma 0)}
    {rS₂ : AuxNode (sigma 0)}
    {rU₀ : EnumNode (f 0)} {rU₁ : OneNode (f 0)}
    {rU₂ : AuxNode (f 0)}
    (hS₀ : InfiniteStrongPicture S₀ sigma (.enum (sigma 0) rS₀))
    (hS₁ : InfiniteStrongPicture S₁ sigma (.one (sigma 0) rS₁))
    (hS₂ : InfiniteStrongPicture S₂ sigma (.aux (sigma 0) rS₂))
    (hU₀ : InfiniteStrongPicture U₀ f (.enum (f 0) rU₀))
    (hU₁ : InfiniteStrongPicture U₁ f (.one (f 0) rU₁))
    (hU₂ : InfiniteStrongPicture U₂ f (.aux (f 0) rU₂))
    (hsigma : StrictMono sigma) (hf : StrictMono f) :
    ∃ (V₀ : Set CoordNode),
      ∃ hV₀ : InfiniteStrongPicture V₀ (fun i => f (sigma i))
        (.enum (f (sigma 0))
          (infiniteEnumCanonicalMap hU₀ hU₁ hU₂ (sigma 0) rS₀).val),
        infiniteEnumImage hU₀ hU₁ hU₂ S₀ ⊆ V₀ := by
  obtain ⟨V, hV, _, hE⟩ :=
    exists_infiniteEnum_image_completion_with_subset
      hS₀ hS₁ hS₂ hU₀ hU₁ hU₂ hsigma hf
  exact ⟨V, hV, hE⟩

end CoordNode
end ThreeUniformDiaries
