import ThreeUniformDiaries.DiaryFiniteATRFamily
import ThreeUniformDiaries.DiaryLateSingletonATRCodes
import ThreeUniformDiaries.DiaryInjectiveAvoidance

/-!
# Simultaneously avoiding a finite target interval in all singleton types

The first step of the lower-bound stage recursion requires a single
prefix-fixing aux-type-respecting generic self-embedding that avoids
a finite forbidden set for EVERY singleton type over the cut.

The verified finite-family ATR theorem supplies the common
homogeneous embedding for any finite list of actual singleton
envelope sources. We colour every finite source by the same Bool
test on its last real vertex, pulled back through an arbitrary
injective outer map F. For each listed shape the homogeneous
forbidden colour is impossible: an arbitrarily late genuine finite
copy of the SAME source has an outer image above the bound.
No monotonicity of F is used.

This theorem works for any explicitly supplied finite list of
singleton envelopes. Constructing a finite list covering ALL
singleton types of the generic graph at a cut is the separate,
remaining enumeration-of-types step.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- One concrete native singleton source shape over a common cut n.
The terminal ambient vertex may depend on the source. -/
structure SingletonShape (G : GenericEnumerated3Graph) (n : Nat) where
  terminal : Nat
  envelope : FiniteSingletonEnvelope G.graph n terminal

/-- Pass a singleton envelope to the generic finite-family ATR
source interface without introducing any artificial source tail. -/
noncomputable def SingletonShape.protected
    {G : GenericEnumerated3Graph} {n : Nat}
    (S : SingletonShape G n) : ProtectedSource n where
  k := n
  picture := S.envelope.finiteEnum
  cut_le := Nat.le_succ n

/-- A single aux-type-respecting refinement simultaneously keeps all
genuine prefix-fixed copies of any finite collection of singleton
shapes away from the forbidden initial outer-image interval. The
outer map F is only injective, not ordered. -/
theorem actualFiniteSingletonATR_avoidFamily
    (G : GenericEnumerated3Graph) (n : Nat)
    (F : Nat → Nat) (hF : Function.Injective F)
    (M : Nat) (family : List (SingletonShape G n)) :
    ∃ (u : Embedding G.graph G.graph)
      (hu : u.AuxTypeRespecting),
      (∀ t < n, u t = t) ∧
      ∀ (S : SingletonShape G n), S ∈ family →
        ∀ e : FiniteAuxEmbeddingImage
            S.envelope.finiteEnum.toOrdered3Graph G.graph (n+1),
          (∀ i : Fin (n+1), i.val < n → e.image i = i.val) →
          M < F (u (e.image (Fin.last n))) := by
  classical
  let χ : ∀ A : ProtectedSource n, A.Code G → Bool :=
    fun A e => decide (F (e.image (Fin.last A.k)) ≤ M)
  let sources : List (ProtectedSource n) :=
    family.map (fun S => S.protected)
  obtain ⟨u, hu, hfix, hmono⟩ :=
    actualFiniteAuxRamsey_finiteFamily G n χ sources
  obtain ⟨B, hB⟩ :=
    DiaryLowerBoundAvoidance.eventually_above_after_injective_refinement
      F hF u.toFun u.strictMono.injective M
  refine ⟨u, hu, hfix, ?_⟩
  intro S hS e hefix
  have hmem : S.protected ∈ sources :=
    List.mem_map.mpr ⟨S, hS, rfl⟩
  obtain ⟨color, hcolor⟩ := hmono S.protected hmem
  obtain ⟨v, hvB, eLate, hfixLate, hlast⟩ :=
    G.exists_late_singleton_finiteATRCode S.envelope B
  have hlast' : eLate.image (Fin.last n) = v := by
    simpa only [Fin.last] using hlast
  have hbit : decide (F (u v) ≤ M) = color := by
    have hh := hcolor eLate hfixLate
    simpa only [χ, SingletonShape.protected,
      FiniteAuxEmbeddingImage.postcompose_apply, hlast'] using hh
  have hnot : ¬ F (u v) ≤ M := by
    have hv : M < F (u v) := hB v (Nat.le_of_lt hvB)
    omega
  have hfalse : color = false := by
    have hdec : decide (F (u v) ≤ M) = false := by
      simp [hnot]
    exact hbit.symm.trans hdec
  have hcol := hcolor e hefix
  have hdec :
      decide (F (u (e.image (Fin.last n))) ≤ M) = false := by
    simpa only [χ, SingletonShape.protected,
      FiniteAuxEmbeddingImage.postcompose_apply, hfalse] using hcol
  by_contra hn
  have hle : F (u (e.image (Fin.last n))) ≤ M := by omega
  simp [hle] at hdec

end ATRFiniteDecoder
end ThreeUniformDiaries
