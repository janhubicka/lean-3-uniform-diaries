import ThreeUniformDiaries.FiniteActualCandidateRoots
import ThreeUniformDiaries.FiniteStrongCompletion

/-!
# The actual E2 candidate carrier fixes the canonical auxiliary root

For finite Aemb the E2^- picture contains all nodes of the fixed
initial segment n and all target pair types at selected cuts >= n.
Thus for any genuine source pair (u,v), its target pair type over
the first selected level f(0) belongs to E2^-:

* if n=0, this is a prescribed pair candidate at source cut 0;
* if n>0, f(0)=0 and it belongs to the complete prefix level 0.

Since the completed strong picture has a unique first-level root,
that root must equal each of these target pair types. No separate
root compatibility axiom is needed, including when f(0)>0.
-/

namespace ThreeUniformDiaries
namespace EnumNode

theorem finiteAuxCandidate_root_eq_pairType
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (f : Nat → Nat) (n : Nat)
    (hfix : ∀ j < n, f j = j)
    {S : Set CoordNode} {r : AuxNode (f 0)}
    (hS : CoordNode.FiniteStrongPicture S f (m - 1)
      (.aux (f 0) r))
    (hinc : ∀ x, finiteAuxCandidate A H f n x → x ∈ S)
    (u v : Nat) (huv : u < v) (hvm : v < m) :
    r = H.auxType (f 0) (f u) (f v) := by
  let q := CoordNode.aux (f 0)
    (H.auxType (f 0) (f u) (f v))
  have hq : q ∈ S := by
    by_cases hn : n = 0
    · apply hinc
      exact Or.inr ⟨0, u, v, by omega, Nat.zero_le _,
        huv, hvm, rfl⟩
    · have h0 : f 0 = 0 := hfix 0 (by omega)
      apply hinc
      exact Or.inl ⟨f 0, H.auxType (f 0) (f u) (f v),
        by rw [h0]; omega, rfl⟩
  rcases hS with ⟨_, _, _, hroot, _, _, _⟩
  have hbelow :
      CoordNode.aux (f 0) r ≤ q := hroot q hq
  have heq : CoordNode.aux (f 0) r = q :=
    CoordNode.eq_of_le_of_level_eq hbelow rfl
  dsimp [q] at heq
  cases heq
  rfl

end EnumNode
end ThreeUniformDiaries
