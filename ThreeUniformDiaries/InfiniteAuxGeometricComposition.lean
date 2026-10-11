import ThreeUniformDiaries.InfiniteAuxCompositeSuccessor
import ThreeUniformDiaries.InfiniteAuxCanonicalUniqueness
import ThreeUniformDiaries.InfiniteAuxMeetClosedImage
import ThreeUniformDiaries.RelativeStrongAmbientTransitivity

/-!
# Geometric composition of two actual infinite E2 canonical maps

This is the first complete coordinate of the manuscript's
canonicalcomposition lemma, not just an abstract CanonicalMap identity.

Take the actual image E = f_U[S] of the inner strong auxiliary picture
under the outer genuine auxiliary map, protect and complete it INSIDE U
on the inner selected relative levels sigma, and convert the resulting
relative strong picture to an ambient strong picture V. Exact cone
composition and uniqueness show that the actual canonical E2 map of V
is literally f_U ∘ f_S on every finite auxiliary type node.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Any two genuine infinite strong auxiliary pictures have an actual
strong composite picture whose recursive canonical auxiliary map
coincides on ALL source nodes with the pointwise composite. -/
theorem exists_infiniteAux_geometric_composition
    {S U : Set CoordNode} {sigma f : Nat → Nat}
    {rS : AuxNode (sigma 0)} {rU : AuxNode (f 0)}
    (hS : InfiniteStrongPicture S sigma (.aux (sigma 0) rS))
    (hU : InfiniteStrongPicture U f (.aux (f 0) rU))
    (hsigma : StrictMono sigma) (hf : StrictMono f) :
    ∃ (V : Set CoordNode),
      ∃ hV : InfiniteStrongPicture V (fun i => f (sigma i))
        (.aux (f (sigma 0))
          (infiniteAuxCanonicalMap hU (sigma 0) rS).val),
        ∀ n (a : AuxNode n),
          (infiniteAuxCanonicalMap hV n a).val =
            (infiniteAuxCanonicalMap hU (sigma n)
              (infiniteAuxCanonicalMap hS n a).val).val := by
  let E : Set CoordNode := infiniteAuxImage hU S
  let r : CoordNode :=
    .aux (f (sigma 0)) (infiniteAuxCanonicalMap hU (sigma 0) rS).val
  have hEU : E ⊆ U := infiniteAuxImage_subset hU S
  have hE : MeetClosed E :=
    infiniteAuxImage_meetClosed hU hf S hS.meet_closed
  have hlevels : ∀ x ∈ E,
      ∃ i : Nat, level x = f (sigma i) := by
    intro x hx
    rcases hx with ⟨n, a, ha, rfl⟩
    obtain ⟨i, hi⟩ := hS.selected_levels (.aux n a) ha
    refine ⟨i, ?_⟩
    change f n = f (sigma i)
    change n = sigma i at hi
    rw [hi]
  have hrU : r ∈ U :=
    (infiniteAuxCanonicalMap hU (sigma 0) rS).property
  have hrLevel : level r = f (sigma 0) := rfl
  have hrootLevel : level (CoordNode.aux (f 0) rU) = f 0 := rfl
  have hrBelow : ∀ x ∈ E, r ≤ x := by
    intro x hx
    rcases hx with ⟨n, a, ha, rfl⟩
    have hroot := hS.root_le (.aux n a) ha
    have hcut : a.truncate (sigma 0) = rS := by
      have heq := hroot.2
      change CoordNode.aux (sigma 0) (a.truncate (sigma 0)) =
        CoordNode.aux (sigma 0) rS at heq
      injection heq
    have htr := infiniteAuxCanonicalMap_truncate hU hf
      (sigma 0) n hroot.1 a
    rw [hcut] at htr
    refine ⟨hf.monotone hroot.1, ?_⟩
    change CoordNode.aux (f (sigma 0))
      ((infiniteAuxCanonicalMap hU n a).val.truncate (f (sigma 0))) =
      CoordNode.aux (f (sigma 0))
        (infiniteAuxCanonicalMap hU (sigma 0) rS).val
    exact congrArg (CoordNode.aux (f (sigma 0))) htr
  obtain ⟨V, hEV, hRelative⟩ :=
    exists_relative_infinite_strong_completion
      hU hf hrootLevel E hE hEU sigma hsigma hlevels
      r hrU hrLevel hrBelow
  have hV : InfiniteStrongPicture V (fun i => f (sigma i)) r :=
    relativeInfiniteStrongPicture_to_ambient hU hf hsigma hRelative
  let G : (n : Nat) → AuxNode n → AuxNode (f (sigma n)) :=
    fun n a =>
      (infiniteAuxCanonicalMap hU (sigma n)
        (infiniteAuxCanonicalMap hS n a).val).val
  have hmem : ∀ n (a : AuxNode n),
      CoordNode.aux (f (sigma n)) (G n a) ∈ V := by
    intro n a
    apply hEV
    exact ⟨sigma n, (infiniteAuxCanonicalMap hS n a).val,
      (infiniteAuxCanonicalMap hS n a).property, rfl⟩
  have hGroot : ∀ a : AuxNode 0,
      G 0 a = (infiniteAuxCanonicalMap hU (sigma 0) rS).val := by
    intro a
    change (infiniteAuxCanonicalMap hU (sigma 0)
      (infiniteAuxCanonicalMap hS 0 a).val).val =
      (infiniteAuxCanonicalMap hU (sigma 0) rS).val
    rw [infiniteAuxCanonicalMap_root hS a]
  have hGsucc : ∀ n (a : AuxNode n) (bit : Bool),
      CoordNode.aux (f (sigma n) + 1) ((G n a).succ bit) ≤
        CoordNode.aux (f (sigma (n + 1)))
          (G (n + 1) (a.succ bit)) := by
    intro n a bit
    exact infiniteAuxCanonicalMap_composite_succ
      hS hU hsigma hf n a bit
  have heq := infiniteAuxCanonicalMap_unique_of_cones
    hV G hmem hGroot hGsucc
  exact ⟨V, hV, fun n a => (heq n a).symm⟩

end CoordNode
end ThreeUniformDiaries
