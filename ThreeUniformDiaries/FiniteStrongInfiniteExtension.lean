import ThreeUniformDiaries.InfiniteToFiniteStrongPrefix
import ThreeUniformDiaries.FiniteStrongRootLevel

/-!
# Extend an arbitrary finite strong coordinate picture to infinite height

Given a finite strong coordinate picture S whose first k+1 selected
levels are f(0),...,f(k), construct an infinite strong coordinate
picture U with the SAME selected level map and the SAME first root
that contains S literally.

The proof uses the already verified protected infinite completion
on E=S, rather than an artificial extension of an enumeration.
The next bridge will prove that the first k+1 layers agree, and
that the resulting finite/infinite recursive canonical maps agree.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem finiteStrongPicture_exists_infinite_extension
    {S : Set CoordNode} {f : Nat → Nat} {k : Nat}
    {r : CoordNode}
    (hS : FiniteStrongPicture S f k r)
    (hf : StrictMono f) :
    ∃ U : Set CoordNode,
      S ⊆ U ∧ InfiniteStrongPicture U f r := by
  have hrLevel : level r = f 0 :=
    finiteStrongPicture_root_level hS hf
  obtain ⟨hfinite, hmeet, hroot, hrootle, hlevels, hall, hchildren⟩ := hS
  exact exists_infinite_strong_completion S hmeet f hf
    (fun x hx => by
      obtain ⟨i, _, hi⟩ := hlevels x hx
      exact ⟨i, hi⟩)
    r hrLevel hrootle

end CoordNode
end ThreeUniformDiaries
