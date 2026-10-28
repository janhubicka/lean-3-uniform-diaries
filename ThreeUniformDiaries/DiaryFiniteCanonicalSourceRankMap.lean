import ThreeUniformDiaries.DiaryFiniteCanonicalCausalRoleCensus
import ThreeUniformDiaries.DiaryFiniteMeetEmbedding

/-!
# A genuine total increasing rank map for each canonical source flip

The source-branch rank was previously defined only for vertices
in the bounded interval [0,n). Existing protected-picture and
FiniteMeetEmbedding APIs use a TOTAL Nat -> Nat map.

Extend the actual finite predecessor-count rank by a simple
increasing tail beyond n. The resulting map is strictly
increasing everywhere on Nat, fixes markers 0,1,2, and agrees
EXACTLY with the ranked source node indices below n.

This is bookkeeping for the subsequent protection theorem. It
does not assume or assert preservation of arbitrary mixed full
pair meets, a full S1/S2 target diary, or finite absorption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The actual canonical finite rank on source vertices z<n,
extended to a total strictly increasing map above the finite
target carrier after the source cutoff n. -/
noncomputable def finiteCanonicalSourceRankMap
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (z : Nat) : Nat :=
  if h : z < n then
    (finiteCanonicalNodeIndex DA
      (finiteCanonicalNodeAt DA i z h)).val
  else Fintype.card (FiniteCanonicalSignRootedVertex DA) + (z - n)

/-- On the actual bounded source, this total map is literally
the previously verified finite level-first node rank. -/
@[simp] theorem finiteCanonicalSourceRankMap_of_lt
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (z : Nat) (hzn : z < n) :
    finiteCanonicalSourceRankMap DA i z =
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i z hzn)).val := by
  simp [finiteCanonicalSourceRankMap, hzn]

/-- The total rank map is strictly increasing on ALL naturals:
the actual source ranks occupy a finite initial interval and
the tail begins at the cardinality of that interval. -/
theorem finiteCanonicalSourceRankMap_strictMono
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n) :
    StrictMono (finiteCanonicalSourceRankMap DA i) := by
  apply strictMono_nat_of_lt_succ
  intro z
  by_cases hz : z < n
  · by_cases hzn : z + 1 < n
    · have hSource := finiteCanonicalNodeAt_index_lt
        DA i z (z+1) (by omega) hzn
      simpa only [finiteCanonicalSourceRankMap,
        dif_pos hz, dif_pos hzn] using hSource
    · have hBound := (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i z hz)).isLt
      simp only [finiteCanonicalSourceRankMap,
        dif_pos hz, dif_neg hzn]
      omega
  · have hzn : ¬ z + 1 < n := by omega
    simp only [finiteCanonicalSourceRankMap,
      dif_neg hz, dif_neg hzn]
    omega

/-- The total source map fixes precisely the distinguished
three marker vertices, with no arbitrary renumbering. -/
theorem finiteCanonicalSourceRankMap_marker
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (z : Nat) (hz : z < 3) :
    finiteCanonicalSourceRankMap DA i z = z := by
  have hn3 : 3 ≤ n := DA.prediary.frame.length_ge_three
  have hzn : z < n := by omega
  rw [finiteCanonicalSourceRankMap_of_lt DA i z hzn]
  exact finiteCanonicalMarker_index_of_lt_three DA i z hz hzn

/-- The induced source image is injective as a map on Nat,
not merely on the finite source carrier. -/
theorem finiteCanonicalSourceRankMap_injective
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n) :
    Function.Injective (finiteCanonicalSourceRankMap DA i) :=
  (finiteCanonicalSourceRankMap_strictMono DA i).injective

/-- Every old source vertex lies inside the bounded final
carrier; the total tail starts outside that carrier. -/
theorem finiteCanonicalSourceRankMap_lt_carrier
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (z : Nat) (hzn : z < n) :
    finiteCanonicalSourceRankMap DA i z <
      Fintype.card (FiniteCanonicalSignRootedVertex DA) := by
  rw [finiteCanonicalSourceRankMap_of_lt DA i z hzn]
  exact (finiteCanonicalNodeIndex DA
      (finiteCanonicalNodeAt DA i z hzn)).isLt

end DiaryLeafPriority
end ThreeUniformDiaries
