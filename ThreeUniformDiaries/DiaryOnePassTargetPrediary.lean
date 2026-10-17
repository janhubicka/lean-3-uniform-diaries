import ThreeUniformDiaries.DiaryOnePassGlobalV3
import ThreeUniformDiaries.DiaryOnePassTargetV1Witness
import ThreeUniformDiaries.DiaryOnePassTargetV2Witness
import ThreeUniformDiaries.DiaryOnePassTargetV1Coherence
import ThreeUniformDiaries.DiaryOnePassTargetV2Coherence
import ThreeUniformDiaries.DiaryOnePassRoleCoverage

/-!
# The genuine one-pass target satisfies ALL source pre-diary axioms

This packages the earlier independently checked target components:
* valid roles on every actual target vertex and all E-permitted edges;
* full positive-cone coherence and exact numerical witnesses for both
  original and fresh 1-/2-split vertices;
* BOTH real target V3 leaf marker equivalences, now derived from the
  source LexEarlier preservation theorem rather than postulated.

The candidate is therefore an actual RolePrediary. This theorem
does NOT assert the two S1/S2 meet axioms needed for a full diary,
nor the protected flip absorption condition of the Ramsey proof.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- The one-pass finite-block construction sends every V/E source
pre-diary to a genuine V/E target pre-diary, without source S1/S2. -/
theorem onePassRawTarget_isPrediary
    (P : RolePrediary H) :
    RolePrediary (onePassRawTarget H) := by
  have hE := onePassRawTarget_role_and_E P
  have hV3 := onePassRawTarget_complete_V3 P
  exact {
    role_valid := hE.1
    one_split_coherent := onePassRawTarget_one_split_coherent P
    one_split_witness := onePassRawTarget_one_split_witness P
    two_split_coherent := onePassRawTarget_two_split_coherent P
    two_split_witness := onePassRawTarget_two_split_witness P
    leaf_marker_one := hV3.1
    leaf_marker_two := hV3.2
    edge_ordered := hE.2.1
    permitted_edge := hE.2.2
  }

end DiaryLeafPriority
end ThreeUniformDiaries
