import ThreeUniformDiaries.DiaryFiniteCanonicalCausalTwoSplitWitness
import ThreeUniformDiaries.DiaryFiniteCanonicalCausalFiniteFrame
import ThreeUniformDiaries.DiaryFiniteCanonicalCausalGlobalVOne
import ThreeUniformDiaries.DiaryFiniteCanonicalCausalGlobalVTwo
import ThreeUniformDiaries.DiaryFiniteCanonicalCausalGlobalV3
import ThreeUniformDiaries.DiaryFiniteCanonicalCausalOneSplitWitness
import ThreeUniformDiaries.DiaryFiniteCanonicalCausalPermittedEdges

/-!
# Complete genuine finite pre-diary from the sign-rooted causal construction

All fields of the manuscript's actual finite V/E pre-diary are now
verified for the concrete Nat-indexed sign-rooted canonical flip
carrier: exact finite edge support, role coverage, global V1 and
V2 positive-class coherence, genuine bounded one- and two-split
witnesses, BOTH literal Devlin V3 marker equivalences on ALL
ordered pairs of actual finite target leaves, and all five E1–E5
edge forms.

The theorem assembles precisely these verified components into
a genuine FiniteRolePrediaryBlock. There is no S1/S2 requirement
on the new cross-branch leaf pairs and no false extension to an
infinite RolePrediary outside the finite frame.

It DOES NOT assert the final finite structure is a full diary;
a later relative one-pass protected completion may repair the
cross-branch S1/S2 deficits. In particular neither protected
mixed numerical meets of all original branches nor universal
finite flip absorption follow merely from this pre-diary theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The ACTUAL canonical sign-rooted causal marker graph is
a complete finite V/E pre-diary on its exactly enumerated
finite carrier, including genuine bounded V1/V2 witnesses
and literal V3 on every pair of target leaves. -/
theorem finiteCanonicalCausalMarkerGraph_finitePrediary
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n) :
    FiniteRolePrediaryBlock
      (finiteCanonicalCausalMarkerGraph DA)
      (Fintype.card (FiniteCanonicalSignRootedVertex DA)) := by
  exact {
    frame := finiteCanonicalCausalMarkerGraph_finiteFrame DA
    role_valid := finiteCanonicalCausalMarkerGraph_role_valid DA
    one_split_coherent :=
      finiteCanonicalCausalMarkerGraph_global_oneSplit_coherent DA
    one_split_witness :=
      finiteCanonicalCausalMarkerGraph_global_oneSplit_witness DA
    two_split_coherent :=
      finiteCanonicalCausalMarkerGraph_global_twoSplit_coherent DA
    two_split_witness :=
      finiteCanonicalCausalMarkerGraph_global_twoSplit_witness DA
    leaf_marker_one :=
      (finiteCanonicalCausalMarkerGraph_complete_finite_V3 DA).1
    leaf_marker_two :=
      (finiteCanonicalCausalMarkerGraph_complete_finite_V3 DA).2
    permitted_edge :=
      finiteCanonicalCausalMarkerGraph_permitted_edge DA
  }

end DiaryLeafPriority
end ThreeUniformDiaries
