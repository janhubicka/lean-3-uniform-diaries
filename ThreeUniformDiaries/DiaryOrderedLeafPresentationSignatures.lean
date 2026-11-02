import ThreeUniformDiaries.DiarySharpUnlabelledConditionalUpper

/-!
# Track C: partition unmarked diary sources by increasing leaf presentations

The printed big Ramsey theorem uses "diaries of A" with A an
UNORDERED finite 3-hypergraph. The source-level diary definition,
however, is for an INCREASING ordered presentation. An unordered
hypergraph can have several nonisomorphic increasing presentations.

For each genuine unmarked full finite diary source we define a
literal FINITE EDGE SIGNATURE of its ordered leaf reduct: list all
increasing triples of genuine leaves and relabel each old leaf
by its ordinal rank among the selected leaves. The data record
is therefore independent of the numerical gaps between leaves
and distinguishes distinct ordered presentations.

We prove that the already verified finite genuine unmarked
source count splits as a finite sum over these exact signatures.

This is an exact finite partition, NOT a claim that every
possible ordered presentation is realised by a full diary, nor
that the manuscript's term has been repaired. The full sharp
upper theorem still requires independent geometric factorisation;
the exact lower bound still requires countable unavoidability.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- The ordinal position of a genuine source leaf in the
increasing enumeration of all the source's genuine leaves.
No selected leaf is identified by its old numerical index. -/
noncomputable def ProtectedSource.leafOrderRank
    (S : ProtectedSource 0) (i : Fin (S.k + 1)) : Nat := by
  classical
  exact (S.leafPositions.filter (fun j => j < i)).card

/-- Literal increasing edge signature of the FULL ordered leaf
reduct of a finite enumerated diary source. This is a finite set
of increasing rank triples; old gaps and split positions are
discarded, while the intrinsic increasing order is retained. -/
noncomputable def ProtectedSource.orderedLeafEdgeSignature
    (S : ProtectedSource 0) : Finset (Nat × Nat × Nat) := by
  classical
  let L := S.leafPositions
  exact (((L.product L).product L).filter
    (fun p =>
      p.1.1 < p.1.2 ∧ p.1.2 < p.2 ∧
      S.picture.triple p.1.1.val p.1.2.val p.2.val = true)).image
    (fun p =>
      (S.leafOrderRank p.1.1,
       S.leafOrderRank p.1.2,
       S.leafOrderRank p.2))

/-- All ordered leaf-presentation signatures actually realised by
one of the verified deduplicated genuine unmarked diary sources
of A. Unused impossible signatures are not added. -/
noncomputable def allRealizedOrderedLeafPresentations
    {a : Nat} (A : EnumNode a) :
    Finset (Finset (Nat × Nat × Nat)) := by
  classical
  exact (allGenuineUnmarkedDiarySources A).image
    (fun S => S.orderedLeafEdgeSignature)

/-- Exact finite partition of the genuine unmarked diary count
by the REAL ordered-leaf presentations. In particular, the
correct diary number for an UNORDERED A is a sum over its
increasing presentations, never the diary count of an arbitrarily
chosen single presentation. -/
theorem unmarkedDiaryCount_eq_sum_ordered_presentations
    {a : Nat} (A : EnumNode a) :
    (allGenuineUnmarkedDiarySources A).card =
      ∑ P ∈ allRealizedOrderedLeafPresentations A,
        ((allGenuineUnmarkedDiarySources A).filter
          (fun S => S.orderedLeafEdgeSignature = P)).card := by
  classical
  let U := allGenuineUnmarkedDiarySources A
  let P := allRealizedOrderedLeafPresentations A
  have hMaps :
      (U : Set (ProtectedSource 0)).MapsTo
        (fun S : ProtectedSource 0 => S.orderedLeafEdgeSignature)
        (P : Set (Finset (Nat × Nat × Nat))) := by
    intro S hS
    exact Finset.mem_image.mpr ⟨S, hS, rfl⟩
  exact Finset.card_eq_sum_card_fiberwise hMaps

/-- The four increasing presentations of the unordered four-vertex
3-hypergraph with exactly one hyperedge are determined by the
isolated vertex's position. This finite combinatorial regression
does not assume these four presentations have equal diary counts. -/
def oneTripleFourVertexOrderedSignature
    (isolated : Fin 4) : Finset (Nat × Nat × Nat) :=
  if isolated.val = 0 then {(1,2,3)}
  else if isolated.val = 1 then {(0,2,3)}
  else if isolated.val = 2 then {(0,1,3)}
  else {(0,1,2)}

/-- An unordered 3-edge plus one isolated vertex has FOUR
different increasing edge signatures; equivalently 4!/6=4
because its automorphism group has order six. -/
theorem oneTripleFourVertexOrderedSignatures_card :
    (((Finset.univ : Finset (Fin 4)).image
      oneTripleFourVertexOrderedSignature)).card = 4 := by
  decide

end ATRFiniteDecoder
end ThreeUniformDiaries
