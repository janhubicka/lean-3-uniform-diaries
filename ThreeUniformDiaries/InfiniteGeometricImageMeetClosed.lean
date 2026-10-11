import ThreeUniformDiaries.InfiniteOneFullMeets
import ThreeUniformDiaries.InfiniteEnumFullMeets

/-!
# Meet-closed images for the genuine E1 and E0 geometric canonical maps

The full source-tree-meet preservation theorems now hold in all three
coordinate sorts. This file discharges the remaining two literal
image-closure obligations, supplementing InfiniteAuxMeetClosedImage.

Each image lies inside its supplied infinite strong picture. A
meet-closed source set has a meet-closed actual geometric image,
including for nodes of different source heights and arbitrarily
skipped ambient levels.

No assertion that the image is itself a strong subtree is used:
strong completion inside a *given* coordinate picture remains separate.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Genuine geometric singleton-coordinate image of a source node set. -/
def infiniteOneImage
    {S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₁ : OneNode (f 0)} {r₂ : AuxNode (f 0)}
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (E : Set CoordNode) : Set CoordNode :=
  {x | ∃ (n : Nat) (a : OneNode n),
    CoordNode.one n a ∈ E ∧
    x = CoordNode.one (f n) (infiniteOneCanonicalMap h₁ h₂ n a).val}

/-- Actual singleton images stay in the given strong singleton tree. -/
theorem infiniteOneImage_subset
    {S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₁ : OneNode (f 0)} {r₂ : AuxNode (f 0)}
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (E : Set CoordNode) :
    infiniteOneImage h₁ h₂ E ⊆ S₁ := by
  intro x hx
  rcases hx with ⟨n, a, _, rfl⟩
  exact (infiniteOneCanonicalMap h₁ h₂ n a).property

/-- The genuine singleton-coordinate image preserves meet closure. -/
theorem infiniteOneImage_meetClosed
    {S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₁ : OneNode (f 0)} {r₂ : AuxNode (f 0)}
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f)
    (E : Set CoordNode) (hE : MeetClosed E) :
    MeetClosed (infiniteOneImage h₁ h₂ E) := by
  intro x y hx hy
  rcases hx with ⟨N, u, hu, rfl⟩
  rcases hy with ⟨M, v, hv, rfl⟩
  let n := meetLevel (.one N u) (.one M v)
  have hsource : CoordNode.one n (u.truncate n) ∈ E := by
    simpa only [n, meet, CoordNode.truncate] using (hE hu hv)
  refine ⟨n, u.truncate n, hsource, ?_⟩
  exact infiniteOneCanonicalMap_preserves_meet h₁ h₂ hf u v

/-- Every actual singleton-coordinate image lies on a selected level. -/
theorem infiniteOneImage_selectedLevels
    {S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₁ : OneNode (f 0)} {r₂ : AuxNode (f 0)}
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (E : Set CoordNode) (x : CoordNode)
    (hx : x ∈ infiniteOneImage h₁ h₂ E) :
    ∃ n : Nat, level x = f n := by
  rcases hx with ⟨n, a, _, rfl⟩
  exact ⟨n, rfl⟩

/-- Genuine geometric enumeration-coordinate image of a source node set. -/
def infiniteEnumImage
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (E : Set CoordNode) : Set CoordNode :=
  {x | ∃ (n : Nat) (a : EnumNode n),
    CoordNode.enum n a ∈ E ∧
    x = CoordNode.enum (f n)
      (infiniteEnumCanonicalMap h₀ h₁ h₂ n a).val}

/-- Actual enumeration images stay in the given strong enumeration tree. -/
theorem infiniteEnumImage_subset
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (E : Set CoordNode) :
    infiniteEnumImage h₀ h₁ h₂ E ⊆ S₀ := by
  intro x hx
  rcases hx with ⟨n, a, _, rfl⟩
  exact (infiniteEnumCanonicalMap h₀ h₁ h₂ n a).property

/-- The genuine enumeration-coordinate image preserves meet closure. -/
theorem infiniteEnumImage_meetClosed
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f)
    (E : Set CoordNode) (hE : MeetClosed E) :
    MeetClosed (infiniteEnumImage h₀ h₁ h₂ E) := by
  intro x y hx hy
  rcases hx with ⟨N, u, hu, rfl⟩
  rcases hy with ⟨M, v, hv, rfl⟩
  let n := meetLevel (.enum N u) (.enum M v)
  have hsource : CoordNode.enum n (u.truncate n) ∈ E := by
    simpa only [n, meet, CoordNode.truncate] using (hE hu hv)
  refine ⟨n, u.truncate n, hsource, ?_⟩
  exact infiniteEnumCanonicalMap_preserves_meet h₀ h₁ h₂ hf u v

/-- Every actual enumeration-coordinate image lies on a selected level. -/
theorem infiniteEnumImage_selectedLevels
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : InfiniteStrongPicture S₀ f (.enum (f 0) r₀))
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (E : Set CoordNode) (x : CoordNode)
    (hx : x ∈ infiniteEnumImage h₀ h₁ h₂ E) :
    ∃ n : Nat, level x = f n := by
  rcases hx with ⟨n, a, _, rfl⟩
  exact ⟨n, rfl⟩

end CoordNode
end ThreeUniformDiaries
