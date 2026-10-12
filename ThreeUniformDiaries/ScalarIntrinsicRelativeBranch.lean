import ThreeUniformDiaries.ScalarCanonicalFinitePictures
import ThreeUniformDiaries.ScalarAnchoredInitialTypes
import ThreeUniformDiaries.FiniteRelativeCarrier

/-!
# Genuine intrinsic finite F_I maps preserve K_I after scalar decoding

An actual finite scalar approximation of the glued E0/E1/E2 tree
can have many infinite realizers. The previous modules constructed
its three finite coordinate carriers and a canonical increasing
level function using ONLY the approximation.

If the finite approximation admits a realizer preserving the identity
stem of scalar source height n+1, its canonical finite F_I branch
action preserves the entire relative K_I carrier. In particular this
is not just a colouring defined on copies along the source g_A branch,
nor a definition that needs a chosen infinite future level map.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Milliken
open Milliken.GeneralTree
open ThreeUniformDiaries.CoordNode

/-- On an approximation with an identity-protected scalar stem,
the canonical finite geometric decoder gives an honest K_I action
on EVERY relative branch node whose last source index is at most k.

All hypotheses are explicitly about the actual scalar approximation
and the finite parameters n,k,I; the strong pictures and branch map
are obtained, not postulated. -/
theorem protectedScalarApprox_exists_canonicalRelativeBranchMap
    (k n : Nat)
    (a : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2))
    (hnk : n ≤ k + 1)
    (hvalid : ∃ S : StrongSubtree CoordNode.rootGluedAmbientTree,
      r (k + 2) S = a ∧
      r (n + 1) S = r (n + 1) scalarIdentity)
    (I : EnumNode n) :
    let g := canonicalFiniteLevelMap k a
    ∃ (r₀ : EnumNode (g 0))
      (r₁ : OneNode (g 0))
      (r₂ : AuxNode (g 0))
      (h₀ : FiniteStrongPicture ((finiteTypedCarrier k a).carrier 0)
        g k (.enum (g 0) r₀))
      (h₁ : FiniteStrongPicture ((finiteTypedCarrier k a).carrier 1)
        g k (.one (g 0) r₁))
      (h₂ : FiniteStrongPicture ((finiteTypedCarrier k a).carrier 2)
        g k (.aux (g 0) r₂)),
        ∀ B : EnumerationBranchNode, ∀ hB : B.last ≤ k,
          InRelativeBranchGraph I B →
          InRelativeBranchGraph I
            (finiteStrongPicture_branchMap h₀ h₁ h₂ B hB) := by
  obtain ⟨S, hSa, hstem⟩ := hvalid
  have hS : a.carrier = S.initialPart (k + 2) :=
    congrArg FiniteApprox.carrier hSa.symm
  obtain ⟨hroot, hfixS⟩ :=
    anchoredScalar_root_and_levels S n hstem
  have hlevel0 : S.levels 0 = 0 :=
    CoordNode.millikenStrong_levels_zero_of_root S hroot
  have hrootmem : (none : WithBot CoordNode) ∈ S.carrier := by
    rw [← hroot]
    exact S.root_mem
  have hroota : (none : WithBot CoordNode) ∈ a.carrier := by
    rw [hS]
    refine ⟨hrootmem, 0, (by omega), ?_⟩
    change CoordNode.rootGluedAmbientTree.level
      (none : WithBot CoordNode) = S.levels 0
    rw [hlevel0]
    exact CoordNode.rootGluedAmbientTree.level_root
  obtain ⟨r₀, r₁, r₂, h₀, h₁, h₂⟩ :=
    finiteCode_has_canonical_pictures k a hroota
  let g := canonicalFiniteLevelMap k a
  have hg : StrictMono g := canonicalFiniteLevelMap_strictMono k a
  have hfix : ∀ i < n, g i = i := by
    intro i hi
    have hik : i ≤ k := by omega
    rw [canonicalFiniteLevelMap_eq_realizer k a S hS i hik]
    exact hfixS i hi
  have hfull : ∀ j : Nat, j < n →
      ∀ x : CoordNode, CoordNode.level x = j →
        x ∈ (finiteTypedCarrier k a).carrier (CoordNode.sort x) := by
    intro j hj x hx
    have hmem :
        (some x : WithBot CoordNode) ∈ S.carrier :=
      anchoredScalar_full_type_prefix S n hstem j hj x hx
    have hlevel : S.levels (j + 1) = j + 1 := by
      have hh := sourceLevels_eq_of_approx_eq S scalarIdentity
        (n + 1) hstem (j + 1) (by omega)
      simpa only [scalarIdentity, identityStrongSubtree_levels] using hh
    have hpart : (some x : WithBot CoordNode) ∈ S.initialPart (k + 2) := by
      refine ⟨hmem, j + 1, (by omega), ?_⟩
      change CoordNode.rootGluedAmbientTree.level
        (x : WithBot CoordNode) = S.levels (j + 1)
      rw [CoordNode.rootGluedAmbient_level_coe, hx, hlevel]
    have ha : (some x : WithBot CoordNode) ∈ a.carrier := by
      rw [hS]
      exact hpart
    change CoordNode.sort x = CoordNode.sort x ∧
      (some x : WithBot CoordNode) ∈ a.carrier
    exact ⟨rfl, ha⟩
  have hfull₀ : 0 < n → ∀ x : EnumNode 0,
      CoordNode.enum 0 x ∈ (finiteTypedCarrier k a).carrier 0 := by
    intro hn x
    exact hfull 0 hn (.enum 0 x) rfl
  have hfull₁ : 0 < n → ∀ x : OneNode 0,
      CoordNode.one 0 x ∈ (finiteTypedCarrier k a).carrier 1 := by
    intro hn x
    exact hfull 0 hn (.one 0 x) rfl
  have hfull₂ : 0 < n → ∀ x : AuxNode 0,
      CoordNode.aux 0 x ∈ (finiteTypedCarrier k a).carrier 2 := by
    intro hn x
    exact hfull 0 hn (.aux 0 x) rfl
  refine ⟨r₀, r₁, r₂, h₀, h₁, h₂, ?_⟩
  intro B hB hrel
  exact finiteBranchMap_preserves_relative_carrier
    h₀ h₁ h₂ hg hfix hnk
      hfull₀ hfull₁ hfull₂ I B hB hrel

end ATRFiniteDecoder
end ThreeUniformDiaries
