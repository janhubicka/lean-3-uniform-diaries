import ThreeUniformDiaries.DiaryGappySourceI3TwoSplit
import ThreeUniformDiaries.DiaryGappySourceI2Transfer
import ThreeUniformDiaries.DiaryOneSplitI2WitnessTransfer
import ThreeUniformDiaries.DiaryTwoSplitI3WitnessTransfer

/-!
# The actual pre-embedding split calculations

This applies the verified I1/I2/I3 stabilisation of a genuine
unordered outer hypergraph embedding to any type-respecting,
possibly gappy diary-to-generic induced source map.

* At a one-split, native I2 at the predecessor diary cut and
  actual induced edge reflection give the exact placement interval.
* V/E/S then identifies every source witness class through the
  successor cut. The genuine gappy I2 successor theorem supplies
  target class agreement and yields independence of all witnesses.
* At a two-split, the already verified genuine diary I3 transfer
  and induced reflection give placement; the V/E/S two-split
  classes and successor-cut I3 make every witness comparison
  determine the same target full pair-type meet.

The outer embedding F is NEVER assumed order preserving, and no
type-meet preservation through skipped enumeration levels is used.

This verifies the local split-image construction, not yet the
global pre-embedding, marker flips or lower-bound unavoidability.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph
namespace UnorderedEmbedding

open DiaryLeafPriority

/-- Every singleton meet i under the genuinely stabilised diary
embedding falls in the correct predecessor interval. There are
no extra target-type assumptions: I2 supplies the lower bound,
while the induced target embedding reflects the first source
edge disagreement at the actual split vertex. -/
theorem stabilisedSource_oneSplit_target_placement
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    {H : Ordered3Graph Nat}
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (i u v : Nat)
    (hi : 0 < i) (hiu : i < u) (hiv : i < v)
    (hmeet : H.oneMeetLevel u v = i) :
    let φ := stabilisedSource G K F ψ
    φ (i-1) < K.oneMeetLevel (φ u) (φ v) ∧
      K.oneMeetLevel (φ u) (φ v) ≤ φ i := by
  let φ := stabilisedSource G K F ψ
  have hsource : H.SameOneTypeBelow i u v := by
    simpa only [hmeet] using H.oneMeetLevel_agree u v
  have htarget : K.SameOneTypeBelow (φ (i-1)+1) (φ u) (φ v) :=
    stabilisedOrdered_oneType_of_source G K F ψ hψ i u v
      hi (by omega) (by omega) hsource
  exact oneSplit_target_placement φ i u v
    hi hiu hiv hmeet htarget

/-- Any two leaf comparisons witnessing the same one-split i
give exactly the same target singleton meet under the ACTUAL
stabilised embedding. Source witness-class equivalence follows
from the diary V/E/S axioms and target equivalence from gappy I2. -/
theorem stabilisedSource_oneSplit_witness_independent
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    {H : Ordered3Graph Nat}
    (D : RoleDiary H)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (i u v u' v' : Nat)
    (hi : IsOneSplit H i)
    (hu : IsLeaf H u) (hv : IsLeaf H v)
    (hu' : IsLeaf H u') (hv' : IsLeaf H v')
    (hiu : i < u) (hiv : i < v)
    (hiu' : i < u') (hiv' : i < v')
    (hmeet : H.oneMeetLevel u v = i)
    (hmeet' : H.oneMeetLevel u' v' = i) :
    let φ := stabilisedSource G K F ψ
    K.oneMeetLevel (φ u') (φ v') =
      K.oneMeetLevel (φ u) (φ v) := by
  let φ := stabilisedSource G K F ψ
  have hPlace := stabilisedSource_oneSplit_target_placement
    G K F ψ hψ i u v (by have h := hi.1; omega)
    hiu hiv hmeet
  have hI2 :
      ∀ a b : Nat, i < a → i < b →
        IsLeaf H a → IsLeaf H b →
        H.SameOneTypeBelow (i+1) a b →
        K.SameOneTypeBelow (φ i+1) (φ a) (φ b) := by
    intro a b hia hib _ _ hSame
    exact stabilisedOrdered_oneType_of_source_succ
      G K F ψ hψ i a b (by omega) (by omega) hSame
  exact D.oneSplit_target_witness_independent_of_I2
    φ i u v u' v' hi hu hv hu' hv'
    hiu hiv hiu' hiv' hmeet hmeet'
    hI2 hPlace.2

/-- All comparisons of leaf pairs witnessing the same genuine
diary two-split have one common target full pair meet. The
source next-cut two-type equivalences are derived from V/E/S,
and the target equivalences and placement are supplied by the
fully verified, gap-safe fused diary I3 and induced reflection. -/
theorem stabilisedSource_twoSplit_all_witnesses
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    {H : Ordered3Graph Nat}
    (D : RoleDiary H)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (i a b c d a' b' c' d' : Nat)
    (hi : IsTwoSplit H i)
    (hia : i < a) (hic : i < c)
    (hia' : i < a') (hic' : i < c')
    (hab : a < b) (hcd : c < d)
    (hab' : a' < b') (hcd' : c' < d')
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (ha' : IsLeaf H a') (hb' : IsLeaf H b')
    (hc' : IsLeaf H c') (hd' : IsLeaf H d')
    (hmeet : H.twoMeetLevel a b c d = i)
    (hmeet' : H.twoMeetLevel a' b' c' d' = i) :
    let φ := stabilisedSource G K F ψ
    K.twoMeetLevel (φ a') (φ b') (φ c') (φ d') =
      K.twoMeetLevel (φ a) (φ b) (φ c) (φ d) := by
  let φ := stabilisedSource G K F ψ
  have hPlace := stabilisedSource_twoSplit_target_placement
    G K F D ψ hψ i a b c d
    (by have h := hi.1; omega) hia hic hab hcd
    ha hb hc hd hmeet
  have hI3 :
      ∀ u v w z : Nat,
        i < u → u < v → i < w → w < z →
        IsLeaf H u → IsLeaf H v → IsLeaf H w → IsLeaf H z →
        H.SameTwoTypeBelow (i+1) u v w z →
        K.SameTwoTypeBelow (φ i+1)
          (φ u) (φ v) (φ w) (φ z) := by
    intro u v w z hiu huv hiw hwz hu hv hw hz hSame
    have h :=
      (stabilisedSource_diaryLeafPairType_orientation
        G K F D ψ hψ (i+1) u v w z
        (by have hbound := hi.1; omega)
        (by omega) (by omega) huv hwz
        hu hv hw hz hSame).1
    have hp : i+1-1 = i := by omega
    simpa only [hp] using h
  exact D.twoSplit_target_witness_independent_of_I3
    φ i a b c d a' b' c' d' hi
    hia hic hia' hic' hab hcd hab' hcd'
    ha hb hc hd ha' hb' hc' hd'
    hmeet hmeet' hI3 hPlace.2

end UnorderedEmbedding
end Ordered3Graph
end ThreeUniformDiaries
