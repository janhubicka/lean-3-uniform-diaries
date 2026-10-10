import ThreeUniformDiaries.FiniteStrongCompletion
import ThreeUniformDiaries.FiniteOneMeetClosure
import ThreeUniformDiaries.FiniteEnumMeetClosure

/-!
# The E1 and E0 candidate sets determine the finite canonical roots

The first selected singleton node must be the actual target 1-type
of every source vertex, and the first selected enumeration node must
be the target initial segment at f(0). Both facts follow from literal
candidate inclusion in the completed strong pictures:

* when n=0 these are explicit selected-cut candidates;
* when n>0, f(0)=0 and the entire ambient root level is prescribed.

No global zero-extension assumption, no additional compatibility
hypothesis, and no abstract CanonicalMap structure are required.
-/

namespace ThreeUniformDiaries
namespace EnumNode

theorem finiteOneCandidate_root_eq_vertexType
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (f : Nat → Nat) (n : Nat)
    (hfix : ∀ j < n, f j = j)
    {S : Set CoordNode} {r : OneNode (f 0)}
    (hS : CoordNode.FiniteStrongPicture S f (m - 1)
      (.one (f 0) r))
    (hinc : ∀ x, finiteOneCandidate A H f n x → x ∈ S)
    (v : Nat) (hvm : v < m) :
    r = H.oneType (f 0) (f v) := by
  let q := CoordNode.one (f 0) (H.oneType (f 0) (f v))
  have hq : q ∈ S := by
    by_cases hn : n = 0
    · apply hinc
      exact Or.inr ⟨0, v, by omega, Nat.zero_le _, hvm, rfl⟩
    · have h0 : f 0 = 0 := hfix 0 (by omega)
      apply hinc
      exact Or.inl ⟨f 0, H.oneType (f 0) (f v),
        by rw [h0]; omega, rfl⟩
  rcases hS with ⟨_, _, _, hroot, _, _, _⟩
  have hbelow : CoordNode.one (f 0) r ≤ q := hroot q hq
  have heq : CoordNode.one (f 0) r = q :=
    CoordNode.eq_of_le_of_level_eq hbelow rfl
  dsimp [q] at heq
  cases heq
  rfl

theorem finiteEnumCandidate_root_eq_initialSegment
    {N : Nat} (H : EnumNode N)
    (f : Nat → Nat) (n m : Nat) (hm : 0 < m)
    (hfix : ∀ j < n, f j = j)
    {S : Set CoordNode} {r : EnumNode (f 0)}
    (hS : CoordNode.FiniteStrongPicture S f (m - 1)
      (.enum (f 0) r))
    (hinc : ∀ x, finiteEnumCandidate H f n m x → x ∈ S) :
    r = H.truncate (f 0) := by
  let q := CoordNode.enum (f 0) (H.truncate (f 0))
  have hq : q ∈ S := by
    by_cases hn : n = 0
    · apply hinc
      exact Or.inr ⟨0, by omega, hm, rfl⟩
    · have h0 : f 0 = 0 := hfix 0 (by omega)
      apply hinc
      exact Or.inl ⟨f 0, H.truncate (f 0),
        by rw [h0]; omega, rfl⟩
  rcases hS with ⟨_, _, _, hroot, _, _, _⟩
  have hbelow : CoordNode.enum (f 0) r ≤ q := hroot q hq
  have heq : CoordNode.enum (f 0) r = q :=
    CoordNode.eq_of_le_of_level_eq hbelow rfl
  dsimp [q] at heq
  cases heq
  rfl

end EnumNode
end ThreeUniformDiaries
