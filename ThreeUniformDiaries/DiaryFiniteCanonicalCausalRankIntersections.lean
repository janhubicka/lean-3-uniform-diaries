import ThreeUniformDiaries.DiaryFiniteCanonicalCausalFullTarget

/-!
# Exact original-branch intersections survive finite leaf-meet compression

The explicit finite sign-rooted target was obtained from the
countable causal geometry by keeping the images of EVERY genuine
canonical source leaf and then closing under their numerical meets.
A potential danger for flip-feedback analysis would be to
identify two previously distinct source-prefix nodes, or to split
a single shared node into two after reindexing.

Neither occurs. The source -> countable map is a common STRICTLY
increasing one-pass old-image of the original finite causal ranks.
All genuine finite source vertices belong to the generated leaf-meet
support by their bounded genuine split witnesses. On that support
the finite rank is inverse to the increasing enumeration, so equality
of the selected finite images is equivalent to equality of the
ORIGINAL causal node ranks, even for vertices from two different
canonical source flips.

This is the exact branch-intersection interface needed for future
pairwise target-flip correction tests. Crossbranch numerical meets,
positive-parent profiles after completion, and universal feedback
injectivity are NOT asserted.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Whenever two original sign-rooted source nodes have the same
finite causal rank, their images in the final finite full diary
coincide, independent of the dummy-tail choice. This direction
needs no pre-diary or countable-embedding assumptions. -/
theorem canonicalCausalOrbitFiniteSourceMap_eq_of_sourceRank_eq
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n) (bits : Nat → Bool)
    (i j : FiniteCanonicalFlipIndex A n)
    (u v : Nat) (hu : u < n) (hv : v < n)
    (hRank :
      finiteCanonicalSourceRankMap DA i u =
      finiteCanonicalSourceRankMap DA j v) :
    canonicalCausalOrbitFiniteSourceMap DA bits i u =
      canonicalCausalOrbitFiniteSourceMap DA bits j v := by
  let S := canonicalCausalOrbitFiniteSupport DA bits
  let T := canonicalCausalCountableCarrier DA bits
  change finiteSupportLift S n
      (canonicalCausalCountableSourceMap DA bits i) u =
    finiteSupportLift S n
      (canonicalCausalCountableSourceMap DA bits j) v
  rw [finiteSupportLift_of_lt S n
      (canonicalCausalCountableSourceMap DA bits i) u hu,
    finiteSupportLift_of_lt S n
      (canonicalCausalCountableSourceMap DA bits j) v hv]
  exact congrArg (finiteSupportRank S)
    (congrArg (onePassOldImage T) hRank)

/-- No two DIFFERENT actual causal source nodes can become
identified during the explicit finite compression, provided the
one-pass copies are the previously verified full embeddings.

Thus the entire original finite tree of canonical-source prefix
node identifications survives unchanged, not just each separate
branch's induced edge table. -/
theorem canonicalCausalOrbitFiniteSourceMap_eq_iff_sourceRank_eq
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n) (bits : Nat → Bool)
    (hEmb : ∀ i : FiniteCanonicalFlipIndex A n,
      FiniteMeetEmbedding
        ((finiteCanonicalSignRootedFamily DA).graph i)
        (onePassRawTarget (canonicalCausalCountableCarrier DA bits))
        n (canonicalCausalCountableSourceMap DA bits i))
    (i j : FiniteCanonicalFlipIndex A n)
    (u v : Nat) (hu : u < n) (hv : v < n) :
    (canonicalCausalOrbitFiniteSourceMap DA bits i u =
       canonicalCausalOrbitFiniteSourceMap DA bits j v) ↔
    (finiteCanonicalSourceRankMap DA i u =
       finiteCanonicalSourceRankMap DA j v) := by
  classical
  let G := onePassRawTarget (canonicalCausalCountableCarrier DA bits)
  let L := canonicalCausalOrbitFiniteLeaves DA bits
  let S := finiteLeafMeetSupport G L
  have hRange (t : FiniteCanonicalFlipIndex A n) :
      ∀ z : Nat, z < n →
        canonicalCausalCountableSourceMap DA bits t z ∈ S := by
    have hSelected : ∀ z : Nat, 3 ≤ z → z < n →
        IsLeaf ((finiteCanonicalSignRootedFamily DA).graph t) z →
          canonicalCausalCountableSourceMap DA bits t z ∈ L := by
      intro z hz3 hzn hz
      exact canonicalCausalOrbitFiniteLeaves_mem DA bits t
        z hz3 hzn hz
    exact (hEmb t).range_subset_leafMeetSupport
      ((finiteCanonicalSignRootedFamily DA).flip t).target_diary
      L hSelected
  constructor
  · intro hEq
    have hI := finiteSupportLift_spec S n
      (canonicalCausalCountableSourceMap DA bits i)
      (hRange i) u hu
    have hJ := finiteSupportLift_spec S n
      (canonicalCausalCountableSourceMap DA bits j)
      (hRange j) v hv
    have hImages :
        canonicalCausalCountableSourceMap DA bits i u =
        canonicalCausalCountableSourceMap DA bits j v := by
      calc
        canonicalCausalCountableSourceMap DA bits i u =
            finiteSupportIndex S
              (canonicalCausalOrbitFiniteSourceMap DA bits i u) := hI.2.symm
        _ = finiteSupportIndex S
              (canonicalCausalOrbitFiniteSourceMap DA bits j v) :=
              congrArg (finiteSupportIndex S) hEq
        _ = canonicalCausalCountableSourceMap DA bits j v := hJ.2
    exact (onePassOldImage_strictMono
      (canonicalCausalCountableCarrier DA bits)).injective hImages
  · intro hRank
    exact canonicalCausalOrbitFiniteSourceMap_eq_of_sourceRank_eq
      DA bits i j u v hu hv hRank

end DiaryLeafPriority
end ThreeUniformDiaries
