import ThreeUniformDiaries.InfiniteAuxFullMeets

/-!
# Meet-closed auxiliary pictures remain meet-closed under genuine maps

The infinite geometric E2 canonical map preserves exact ambient
tree meets, not only the selected coordinates. Consequently, the
image of any meet-closed set of finite source auxiliary nodes remains
meet closed and lies inside the given infinite strong picture.

These are the precise two facts required for starting the
strong-subtree completion in the auxiliary coordinate of Lemma
canonicalcomposition. The completion *inside* an ambient strong
subtree U remains an independent step.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- The actual image of a set of auxiliary nodes under the infinite
geometric E2 canonical map. -/
def infiniteAuxImage
    {S : Set CoordNode} {f : Nat → Nat}
    {r : AuxNode (f 0)}
    (hS : InfiniteStrongPicture S f (.aux (f 0) r))
    (E : Set CoordNode) : Set CoordNode :=
  {x | ∃ (n : Nat) (a : AuxNode n),
    CoordNode.aux n a ∈ E ∧
    x = CoordNode.aux (f n) (infiniteAuxCanonicalMap hS n a).val}

/-- Every such canonical image node belongs to the ambient strong
coordinate picture. -/
theorem infiniteAuxImage_subset
    {S : Set CoordNode} {f : Nat → Nat}
    {r : AuxNode (f 0)}
    (hS : InfiniteStrongPicture S f (.aux (f 0) r))
    (E : Set CoordNode) :
    infiniteAuxImage hS E ⊆ S := by
  intro x hx
  rcases hx with ⟨n, a, _, rfl⟩
  exact (infiniteAuxCanonicalMap hS n a).property

/-- An arbitrary meet-closed source auxiliary picture is sent to a
meet-closed subset of the genuine infinite geometric strong picture. -/
theorem infiniteAuxImage_meetClosed
    {S : Set CoordNode} {f : Nat → Nat}
    {r : AuxNode (f 0)}
    (hS : InfiniteStrongPicture S f (.aux (f 0) r))
    (hf : StrictMono f)
    (E : Set CoordNode) (hE : MeetClosed E) :
    MeetClosed (infiniteAuxImage hS E) := by
  intro x y hx hy
  rcases hx with ⟨N, u, hu, rfl⟩
  rcases hy with ⟨M, v, hv, rfl⟩
  let n := meetLevel (.aux N u) (.aux M v)
  have hsource : CoordNode.aux n (u.truncate n) ∈ E := by
    simpa only [n, meet, CoordNode.truncate] using
      (hE hu hv)
  refine ⟨n, u.truncate n, hsource, ?_⟩
  exact (infiniteAuxCanonicalMap_preserves_meet hS hf u v).symm

end CoordNode
end ThreeUniformDiaries
