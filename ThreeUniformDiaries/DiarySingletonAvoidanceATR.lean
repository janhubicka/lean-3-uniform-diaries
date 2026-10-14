import ThreeUniformDiaries.DiaryInjectiveAvoidance
import ThreeUniformDiaries.DiaryLateSingletonATRCodes
import ThreeUniformDiaries.DiaryFiniteSingletonATR

/-!
# The forbidden singleton colour cannot survive ATR homogeneity

The lower-bound type-stabilisation proof first needs to push the
tail away from a fixed finite forbidden target interval, although
its outer embedding F need NOT preserve enumeration order.

This is the actual one-envelope avoidance step. Colour genuine
finite ATR images of a fixed singleton envelope by whether the
outer image of their terminal vertex lies in [0,M]. Apply the
unconditional finite singleton ATR theorem. The homogeneous
forbidden colour is impossible: genericity provides arbitrary
late prefix-fixed finite copies of the SAME envelope source, and
injectivity of F after the Ramsey self-embedding guarantees all
sufficiently late vertices leave [0,M].

No infinite zero-extended source maps are coloured, and no
monotonicity of F is assumed.
-/

namespace ThreeUniformDiaries
namespace GenericEnumerated3Graph

open Ordered3Graph

/-- Every finite singleton envelope admits a prefix-fixed ATR
refinement sending ALL its genuine finite prefix-fixed copies
outside the forbidden initial target interval under an arbitrary
injective outer map F. -/
theorem singleton_envelope_avoids_outer_bound
    (G : GenericEnumerated3Graph)
    {n a : Nat} (E : FiniteSingletonEnvelope G.graph n a)
    (F : Nat → Nat) (hF : Function.Injective F)
    (M : Nat) :
    ∃ (u : Embedding G.graph G.graph)
      (hu : u.AuxTypeRespecting),
      (∀ t < n, u t = t) ∧
      ∀ e : FiniteAuxEmbeddingImage
          E.finiteEnum.toOrdered3Graph G.graph (n+1),
        (∀ i : Fin (n+1), i.val < n → e.image i = i.val) →
        M < F (u (e.image ⟨n, Nat.lt_succ_self n⟩)) := by
  classical
  let χ : FiniteAuxEmbeddingImage
      E.finiteEnum.toOrdered3Graph G.graph (n+1) → Bool :=
    fun e => decide
      (F (e.image ⟨n, Nat.lt_succ_self n⟩) ≤ M)
  obtain ⟨u, hu, hfix, color, hcolour⟩ :=
    E.ramsey_for_fixed_prefix G χ
  obtain ⟨B, hB⟩ :=
    DiaryLowerBoundAvoidance.eventually_above_after_injective_refinement
      F hF u.toFun u.strictMono.injective M
  obtain ⟨v, hvB, e, hefix, hlast⟩ :=
    G.exists_late_singleton_finiteATRCode E B
  have hbit : decide (F (u v) ≤ M) = color := by
    simpa only [χ, FiniteAuxEmbeddingImage.postcompose_apply, hlast]
      using hcolour e hefix
  have hnot : ¬ F (u v) ≤ M := by
    have hh : M < F (u v) := hB v (Nat.le_of_lt hvB)
    omega
  have hfalse : color = false := by
    have hdec : decide (F (u v) ≤ M) = false := by
      simp [hnot]
    exact hbit.symm.trans hdec
  refine ⟨u, hu, hfix, ?_⟩
  intro e hefix
  have hcol := hcolour e hefix
  have hdec :
      decide
        (F (u (e.image ⟨n, Nat.lt_succ_self n⟩)) ≤ M) =
          false := by
    simpa only [χ, FiniteAuxEmbeddingImage.postcompose_apply, hfalse]
      using hcol
  by_contra hn
  have hle :
      F (u (e.image ⟨n, Nat.lt_succ_self n⟩)) ≤ M := by omega
  simp [hle] at hdec

end GenericEnumerated3Graph
end ThreeUniformDiaries
