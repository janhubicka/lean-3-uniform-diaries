import ThreeUniformDiaries.ScalarFiniteCanonicalBranchDecoder
import ThreeUniformDiaries.ScalarIntrinsicRelativeBranch

/-!
# The intrinsic scalar finite decoder lands in K_I on protected stems

The finite F_I branch action is now defined as a literal function of
a Milliken finite approximation and a relative branch vertex.
For approximations with the true identity stem, the concrete
three-coordinate geometry forces it to return a genuine relative
K_I vertex. The result is independent of all infinite realizers and
of all finite-picture root or proof witnesses.

This is the well-defined scalar colouring interface used in the ATR
Ramsey theorem; the stronger realization-under-refinement and final
ambient self-embedding remain separate.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Milliken
open Milliken.GeneralTree
open ThreeUniformDiaries.CoordNode

/-- A scalar finite approximation with a protected identity source
stem necessarily contains the newly adjoined scalar root. -/
theorem protectedScalarApprox_root_mem
    (k n : Nat)
    (a : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2))
    (hvalid : ∃ S : StrongSubtree CoordNode.rootGluedAmbientTree,
      r (k + 2) S = a ∧
      r (n + 1) S = r (n + 1) scalarIdentity) :
    (none : WithBot CoordNode) ∈ a.carrier := by
  obtain ⟨S, hSa, hstem⟩ := hvalid
  have hS : a.carrier = S.initialPart (k + 2) :=
    congrArg FiniteApprox.carrier hSa.symm
  have hroot : S.root = (none : WithBot CoordNode) :=
    (anchoredScalar_root_and_levels S n hstem).1
  have hlevel : S.levels 0 = 0 :=
    CoordNode.millikenStrong_levels_zero_of_root S hroot
  rw [hS]
  refine ⟨?_, 0, (by omega), ?_⟩
  · rw [← hroot]
    exact S.root_mem
  · change CoordNode.rootGluedAmbientTree.level
      (none : WithBot CoordNode) = S.levels 0
    rw [hlevel]
    exact CoordNode.rootGluedAmbientTree.level_root

/-- The concrete Option-valued finite scalar decoder maps every
protected input relative K_I vertex to a real relative K_I vertex
(no default/failure branch can occur on the actual Ramsey domain). -/
theorem protectedScalar_decodeFiniteBranch_relative
    (k n : Nat)
    (a : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2))
    (hnk : n ≤ k + 1)
    (hvalid : ∃ S : StrongSubtree CoordNode.rootGluedAmbientTree,
      r (k + 2) S = a ∧
      r (n + 1) S = r (n + 1) scalarIdentity)
    (I : EnumNode n)
    (B : RelativeBranchNode I) (hB : B.val.last ≤ k) :
    ∃ C : RelativeBranchNode I,
      decodeFiniteBranch k a B.val hB = some C.val := by
  have hroot := protectedScalarApprox_root_mem k n a hvalid
  obtain ⟨r₀, r₁, r₂, h₀, h₁, h₂, hpreserve⟩ :=
    protectedScalarApprox_exists_canonicalRelativeBranchMap
      k n a hnk hvalid I
  let C : RelativeBranchNode I :=
    ⟨finiteStrongPicture_branchMap h₀ h₁ h₂ B.val hB,
      hpreserve B.val hB B.property⟩
  refine ⟨C, ?_⟩
  rw [decodeFiniteBranch_root k a B.val hB hroot]
  rw [rootedScalarFiniteBranchMap_eq_of_pictures
    k a hroot h₀ h₁ h₂ B.val hB]

/-- A total relative K_I action on arbitrary scalar finite
approximations: invalid approximations are mapped to none; valid
ones return an actual relative branch vertex, whose carrier
proof is checked by the original finite F_I map. -/
noncomputable def decodeFiniteRelativeBranch
    (k n : Nat) (I : EnumNode n)
    (a : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2))
    (B : RelativeBranchNode I) (hB : B.val.last ≤ k) :
    Option (RelativeBranchNode I) := by
  classical
  exact (decodeFiniteBranch k a B.val hB).bind fun C =>
    if h : InRelativeBranchGraph I C then
      some ⟨C, h⟩
    else none

/-- Every protected genuine scalar finite approximation has a
successful total relative decoder value on every admissible K_I
branch. The output is precisely the real finite F_I code. -/
theorem protectedScalar_decodeFiniteRelativeBranch_some
    (k n : Nat)
    (a : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2))
    (hnk : n ≤ k + 1)
    (hvalid : ∃ S : StrongSubtree CoordNode.rootGluedAmbientTree,
      r (k + 2) S = a ∧
      r (n + 1) S = r (n + 1) scalarIdentity)
    (I : EnumNode n)
    (B : RelativeBranchNode I) (hB : B.val.last ≤ k) :
    ∃ C : RelativeBranchNode I,
      decodeFiniteRelativeBranch k n I a B hB = some C := by
  classical
  obtain ⟨C, hC⟩ :=
    protectedScalar_decodeFiniteBranch_relative
      k n a hnk hvalid I B hB
  refine ⟨C, ?_⟩
  unfold decodeFiniteRelativeBranch
  rw [hC]
  simp [C.property]

end ATRFiniteDecoder
end ThreeUniformDiaries
