import ThreeUniformDiaries.RootGluedFiniteDecoder

/-!
# Finite ATR decoder with the canonical scalar-selected level map

The basic finite strong-picture existence theorem previously returned
an existentially quantified level map. For the relative K_I branch
action it is essential that this map is exactly the normalized map
f(i) = S.levels(i+1)-1 of the GIVEN scalar Milliken witness, not
some alternative extension above the finite approximation.

This strengthens the decoder statement while retaining all three
actual finite-coordinate strongness proofs and exact glued carrier
equality. It does not presume a canonical K_I branch-action theorem.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Decode a height-(k+2) scalar prefix into finite E0/E1/E2 strong
pictures with precisely the scalar witness's coordinate level map. -/
theorem millikenStrong_exists_fixedlevel_finite_vector
    (S : Milliken.GeneralTree.StrongSubtree rootGluedAmbientTree)
    (hroot : S.root = (none : WithBot CoordNode))
    (k : Nat) :
    let f := millikenCoordinateLevels S
    ∃ (F : TypedVectorSubset)
      (r₀ : EnumNode (f 0))
      (r₁ : OneNode (f 0))
      (r₂ : AuxNode (f 0)),
        StrictMono f ∧
        FiniteStrongPicture (F.carrier 0) f k (.enum (f 0) r₀) ∧
        FiniteStrongPicture (F.carrier 1) f k (.one (f 0) r₁) ∧
        FiniteStrongPicture (F.carrier 2) f k (.aux (f 0) r₂) ∧
        S.initialPart (k + 2) = F.glue := by
  let f := millikenCoordinateLevels S
  have hf : StrictMono f :=
    millikenCoordinateLevels_strictMono S
      (millikenStrong_levels_zero_of_root S hroot)
  obtain ⟨r₀, r₁, r₂, h₀, h₁, h₂⟩ :=
    millikenStrong_exists_actual_vector S hroot
  let V := typedVectorOfStrong h₀ h₁ h₂
  let F := V.truncateSelected f (k + 1)
  obtain ⟨hF₀, hF₁, hF₂⟩ :=
    typedVectorStrong_finiteSlice_eq h₀ h₁ h₂ hf k
  have hstrong₀ :
      FiniteStrongPicture (F.carrier 0) f k
        (.enum (f 0) r₀) := by
    rw [hF₀]
    exact infiniteStrongPicture_finitePrefix_strong h₀ hf rfl k
  have hstrong₁ :
      FiniteStrongPicture (F.carrier 1) f k
        (.one (f 0) r₁) := by
    rw [hF₁]
    exact infiniteStrongPicture_finitePrefix_strong h₁ hf rfl k
  have hstrong₂ :
      FiniteStrongPicture (F.carrier 2) f k
        (.aux (f 0) r₂) := by
    rw [hF₂]
    exact infiniteStrongPicture_finitePrefix_strong h₂ hf rfl k
  have hCarrier := millikenStrong_recovered_vector_carrier
    S hroot h₀ h₁ h₂ hf
  have hGlue : V.glue = S.carrier := by
    change (typedVectorOfStrong h₀ h₁ h₂).glue =
      S.carrier at hCarrier
    exact hCarrier
  have hInverse : TypedVectorSubset.ofGlued S.carrier = V := by
    calc
      TypedVectorSubset.ofGlued S.carrier =
          TypedVectorSubset.ofGlued V.glue :=
        congrArg TypedVectorSubset.ofGlued hGlue.symm
      _ = V := TypedVectorSubset.ofGlued_glue V
  have hApprox := millikenStrong_normalized_finitePrefix
    S hroot (k + 1)
  have hFinite : S.initialPart (k + 2) = F.glue := by
    rw [hInverse] at hApprox
    exact hApprox
  exact ⟨F, r₀, r₁, r₂, hf, hstrong₀, hstrong₁, hstrong₂, hFinite⟩

end CoordNode
end ThreeUniformDiaries
