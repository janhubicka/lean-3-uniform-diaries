import ThreeUniformDiaries.ScalarAnchoredInitialTypes
import ThreeUniformDiaries.RootGluedFixedLevelDecoder
import ThreeUniformDiaries.FiniteRelativeCarrier

/-!
# The actual finite relative K_I action decoded from a protected scalar stem

The proof of the ATR Ramsey theorem colours finite *scalar* Milliken
approximations by their actual finite E0/E1/E2 canonical action.
This module verifies that a strong scalar tree retaining the identity
stem of source height n+1 has a genuine finite vector prefix whose
canonical branch map lands inside the complete relative K_I carrier.

The protected first n coordinate levels are checked on the real scalar
root-glued type trees. We do not insert an artificial fixed-prefix
assumption into the decoding operation.

The scalar heterogeneous Milliken theorem and the final compositional
realisation theorem remain separate inputs.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Milliken
open Milliken.GeneralTree
open ThreeUniformDiaries.CoordNode

/-- Every ambient coordinate node at a protected initial level
belongs to the decoded FINITE vector picture, not only to the
original infinite scalar tree. -/
theorem anchoredScalar_finite_vector_full_prefix
    (S : StrongSubtree CoordNode.rootGluedAmbientTree)
    (n k : Nat)
    (hstem : r (n + 1) S = r (n + 1) scalarIdentity)
    (hnk : n ≤ k + 1)
    {f : Nat → Nat}
    {F : CoordNode.TypedVectorSubset}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : FiniteStrongPicture (F.carrier 0) f k (.enum (f 0) r₀))
    (h₁ : FiniteStrongPicture (F.carrier 1) f k (.one (f 0) r₁))
    (h₂ : FiniteStrongPicture (F.carrier 2) f k (.aux (f 0) r₂))
    (hF : S.initialPart (k + 2) = F.glue) :
    ∀ j : Nat, j < n →
      ∀ x : CoordNode, CoordNode.level x = j →
        x ∈ F.carrier (CoordNode.sort x) := by
  intro j hj x hx
  have hmem :
      (some x : WithBot CoordNode) ∈ S.carrier :=
    anchoredScalar_full_type_prefix S n hstem j hj x hx
  have hlevel : S.levels (j + 1) = j + 1 := by
    have h := sourceLevels_eq_of_approx_eq S scalarIdentity
      (n + 1) hstem (j + 1) (by omega)
    simpa only [scalarIdentity, identityStrongSubtree_levels] using h
  have hpart :
      (some x : WithBot CoordNode) ∈ S.initialPart (k + 2) := by
    refine ⟨hmem, j + 1, (by omega), ?_⟩
    change CoordNode.rootGluedAmbientTree.level
      (x : WithBot CoordNode) = S.levels (j + 1)
    rw [CoordNode.rootGluedAmbient_level_coe, hx, hlevel]
  have hglue : (some x : WithBot CoordNode) ∈ F.glue := by
    rw [← hF]
    exact hpart
  exact (F.mem_coordinate_iff_glued (CoordNode.sort x) x rfl).mpr hglue

/-- From every scalar strong subtree preserving the exact first n+1
scalar source levels, construct a genuine finite three-coordinate
strong prefix and prove that its *actual* F_I^S canonical branch
formula preserves the entire relative K_I vertex carrier. -/
theorem anchoredScalar_exists_finiteRelativeBranchMap
    (S : StrongSubtree CoordNode.rootGluedAmbientTree)
    (n k : Nat)
    (hstem : r (n + 1) S = r (n + 1) scalarIdentity)
    (hnk : n ≤ k + 1)
    (I : EnumNode n) :
    let f := CoordNode.millikenCoordinateLevels S
    ∃ (F : CoordNode.TypedVectorSubset)
      (r₀ : EnumNode (f 0))
      (r₁ : OneNode (f 0))
      (r₂ : AuxNode (f 0))
      (hf : StrictMono f)
      (h₀ : FiniteStrongPicture (F.carrier 0) f k (.enum (f 0) r₀))
      (h₁ : FiniteStrongPicture (F.carrier 1) f k (.one (f 0) r₁))
      (h₂ : FiniteStrongPicture (F.carrier 2) f k (.aux (f 0) r₂)),
        S.initialPart (k + 2) = F.glue ∧
        ∀ (B : EnumerationBranchNode) (hB : B.last ≤ k),
          InRelativeBranchGraph I B →
          InRelativeBranchGraph I
            (finiteStrongPicture_branchMap h₀ h₁ h₂ B hB) := by
  obtain ⟨hroot, hfix⟩ :=
    anchoredScalar_root_and_levels S n hstem
  obtain ⟨F, r₀, r₁, r₂, hf, h₀, h₁, h₂, hF⟩ :=
    CoordNode.millikenStrong_exists_fixedlevel_finite_vector S hroot k
  have hfull : ∀ j : Nat, j < n →
        ∀ x : CoordNode, CoordNode.level x = j →
          x ∈ F.carrier (CoordNode.sort x) :=
    anchoredScalar_finite_vector_full_prefix S n k hstem hnk
      h₀ h₁ h₂ hF
  have hfull₀ : 0 < n → ∀ a : EnumNode 0,
      CoordNode.enum 0 a ∈ F.carrier 0 := by
    intro hn a
    exact hfull 0 hn (.enum 0 a) rfl
  have hfull₁ : 0 < n → ∀ a : OneNode 0,
      CoordNode.one 0 a ∈ F.carrier 1 := by
    intro hn a
    exact hfull 0 hn (.one 0 a) rfl
  have hfull₂ : 0 < n → ∀ a : AuxNode 0,
      CoordNode.aux 0 a ∈ F.carrier 2 := by
    intro hn a
    exact hfull 0 hn (.aux 0 a) rfl
  refine ⟨F, r₀, r₁, r₂, hf, h₀, h₁, h₂, hF, ?_⟩
  intro B hB hrel
  exact finiteBranchMap_preserves_relative_carrier
    h₀ h₁ h₂ hf hfix hnk
      hfull₀ hfull₁ hfull₂ I B hB hrel

end ATRFiniteDecoder
end ThreeUniformDiaries
