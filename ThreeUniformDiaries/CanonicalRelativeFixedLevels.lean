import ThreeUniformDiaries.CanonicalRelativeCarrier

/-!
# Fixed selected levels automatically fix every initial finite hypergraph

The finite relative-carrier theorem was stated with two hypotheses:
(1) a canonical level map fixes all indices j<n, and
(2) the canonical image of the initial hypergraph I has the same
first n ordinary vertices as I.

For a genuine CanonicalMap, the second hypothesis follows from the
first by its already verified selected-triple equality: every
increasing triple of indices below n is selected and therefore
retains its original edge bit. This important simplification
eliminates a separate geometric initial-prefix obligation in the
relative K_I part of the Ramsey proof.
-/

namespace ThreeUniformDiaries
namespace CanonicalMap

/-- Fixing all protected selected indices is sufficient to ensure
the full initial-cut property in the relative K_I carrier. -/
theorem fixesRelativeCut_of_fixed_levels
    (F : CanonicalMap) {n : Nat} (I : EnumNode n)
    (hlevels : ∀ j < n, F.level j = j) :
    F.FixesRelativeCut I := by
  refine ⟨hlevels, ?_⟩
  apply EnumNode.ext_triples
  funext a b c
  by_cases hvalid : a < b ∧ b < c ∧ c < n
  · have ha : a < n := by omega
    have hb : b < n := by omega
    have hc : c < n := hvalid.2.2
    have hbit := F.enum_triple_compat I hvalid.1 hvalid.2.1 hc
    rw [hlevels a ha, hlevels b hb, hlevels c hc] at hbit
    change
      (if c < n then (F.mapEnum n I).triple a b c else false) =
        I.triple a b c
    rw [if_pos hc]
    exact hbit
  · have hleft :
        ((F.mapEnum n I).truncate n).triple a b c = false :=
      ((F.mapEnum n I).truncate n).support a b c hvalid
    have hright : I.triple a b c = false :=
      I.support a b c hvalid
    exact hleft.trans hright.symm

/-- A canonical map fixing source levels < n therefore acts on the
whole K_I carrier, without a separate prefix-preservation premise. -/
noncomputable def relativeMapBranch_of_fixed_levels
    (F : CanonicalMap) {n : Nat} (I : EnumNode n)
    (hlevels : ∀ j < n, F.level j = j)
    (B : RelativeBranchNode I) : RelativeBranchNode I :=
  F.relativeMapBranch I (F.fixesRelativeCut_of_fixed_levels I hlevels) B

end CanonicalMap
end ThreeUniformDiaries
