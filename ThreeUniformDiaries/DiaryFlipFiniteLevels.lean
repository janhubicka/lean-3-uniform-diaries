import ThreeUniformDiaries.DiaryFlipBranchAmalgam

/-!
# Finite levels of the diary flip-prefix tree

The tree of branch-prefix control words has two Boolean coordinates
(one for 1-splits and one for 2-splits) at each old source level.
A node of depth n is therefore represented by an element of the
FINITE product (Fin n → Bool) × (Fin n → Bool).

This module builds a finite set of candidate prefix nodes at
each level, and proves it contains the actual nodes of EVERY
diary flip, even for an arbitrarily large or infinite family
of flips. It also gives finite covers for bounded depths.

This is the basic local-finiteness input needed for ordering the
tree by depth, before cross-branch diary completion is attempted.
No unsupported global diary or completion theorem is asserted.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RoleDiary
namespace FlipFamily

variable {A : Ordered3Graph Nat} {ι : Type*}

/-- Build a masked prefix node from genuinely FINITE Boolean
data on Fin n, rather than an unbounded Nat-indexed sequence. -/
def nodeFromFiniteBits
    (n : Nat) (bits : (Fin n → Bool) × (Fin n → Bool)) :
    FlipNode :=
  (n,
    (fun k => if hk : k < n then bits.1 ⟨k, hk⟩ else false,
     fun k => if hk : k < n then bits.2 ⟨k, hk⟩ else false))

/-- The actual node of any branch is encoded by its first n
pairs of control bits. This holds definitionally on both masks. -/
theorem node_eq_nodeFromFiniteBits
    (T : FlipFamily A ι) (i : ι) (n : Nat) :
    T.node i n =
      nodeFromFiniteBits n
        (fun k => T.oneBit i k.val,
         fun k => T.twoBit i k.val) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext k
      by_cases hk : k < n
      · simp [node, nodeFromFiniteBits, hk]
      · simp [node, nodeFromFiniteBits, hk]
    · funext k
      by_cases hk : k < n
      · simp [node, nodeFromFiniteBits, hk]
      · simp [node, nodeFromFiniteBits, hk]

/-- A finite universe of ALL possible double-bit prefix nodes at
depth n. Unused codes are harmless. In particular this does not
require the family of actual diary flips to be finite. -/
noncomputable def levelCandidates (n : Nat) : Finset FlipNode := by
  classical
  exact (Finset.univ :
    Finset ((Fin n → Bool) × (Fin n → Bool))).image
      (nodeFromFiniteBits n)

/-- Every genuine branch has its depth-n node in the same
finite level-candidate set. -/
theorem node_mem_levelCandidates
    (T : FlipFamily A ι) (i : ι) (n : Nat) :
    T.node i n ∈ levelCandidates n := by
  classical
  unfold levelCandidates
  apply Finset.mem_image.mpr
  refine ⟨(fun k : Fin n => T.oneBit i k.val,
           fun k : Fin n => T.twoBit i k.val),
          Finset.mem_univ _, ?_⟩
  exact (T.node_eq_nodeFromFiniteBits i n).symm

/-- Actual nodes up to any fixed level lie in a single finite
set. This is the precise finite-prefix width bound needed
for a future breadth-first enumeration. -/
noncomputable def boundedCandidates (n : Nat) : Finset FlipNode := by
  classical
  exact (Finset.range (n+1)).biUnion levelCandidates

theorem node_mem_boundedCandidates
    (T : FlipFamily A ι) (i : ι)
    (n k : Nat) (hk : k ≤ n) :
    T.node i k ∈ boundedCandidates n := by
  classical
  unfold boundedCandidates
  apply Finset.mem_biUnion.mpr
  exact ⟨k, Finset.mem_range.mpr (by omega),
    T.node_mem_levelCandidates i k⟩

/-- The actual depth-n node set is finite, with no finite-family
assumption. It is included in the explicit candidates above. -/
theorem finite_actual_level
    (T : FlipFamily A ι) (n : Nat) :
    (Set.range (fun i : ι => T.node i n)).Finite := by
  have hsub :
      Set.range (fun i : ι => T.node i n) ⊆
        (levelCandidates n : Set FlipNode) := by
    rintro x ⟨i, rfl⟩
    exact T.node_mem_levelCandidates i n
  exact (Finset.finite_toSet (levelCandidates n)).subset hsub

end FlipFamily
end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
