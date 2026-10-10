import ThreeUniformDiaries.FiniteStrongCompletion

/-!
# The root of a finite strong picture lies on its first selected level

The level of the root was not a field of FiniteStrongPicture, but it
is forced by the other axioms: the root belongs to S, lies below
every node, and S has a node on the initial selected level f(0).

Any retained node at that first selected level must therefore BE
the root, literally. This lemma identifies the typed roots returned
by the abstract finite strong completion when the prescribed E0,
E1, or E2 candidate set contains a first-level node.
-/

namespace ThreeUniformDiaries
namespace CoordNode

theorem finiteStrongPicture_root_level
    {S : Set CoordNode} {f : Nat → Nat} {k : Nat}
    {r : CoordNode}
    (hS : FiniteStrongPicture S f k r)
    (hf : StrictMono f) :
    level r = f 0 := by
  rcases hS with ⟨_, _, hr, hbelow, hlevels, hnonempty, _⟩
  obtain ⟨j, _, hj⟩ := hlevels r hr
  obtain ⟨x, hx, hxl⟩ := hnonempty 0 (Nat.zero_le k)
  have hrx : level r ≤ level x := (hbelow x hx).1
  have h0j : f 0 ≤ f j := hf.monotone (Nat.zero_le j)
  omega

theorem finiteStrongPicture_root_eq_of_first_level
    {S : Set CoordNode} {f : Nat → Nat} {k : Nat}
    {r : CoordNode}
    (hS : FiniteStrongPicture S f k r)
    (hf : StrictMono f)
    (x : CoordNode) (hx : x ∈ S)
    (hl : level x = f 0) :
    r = x := by
  have hbelow : r ≤ x := hS.2.2.2.1 x hx
  apply eq_of_le_of_level_eq hbelow
  exact (finiteStrongPicture_root_level hS hf).trans hl.symm

end CoordNode
end ThreeUniformDiaries
