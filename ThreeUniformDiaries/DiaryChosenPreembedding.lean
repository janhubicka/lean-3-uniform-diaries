import ThreeUniformDiaries.DiaryStabilisedSplitWitnesses
import ThreeUniformDiaries.DiaryPreembeddingIntervalOrder

/-!
# A concrete candidate diary pre-embedding from genuine split witnesses

The V1/V2 witness axioms of a complete role-based diary provide
nonempty finite tuples of leaves witnessing each 1-split and 2-split.
Choose one such tuple for each split. After an unordered external
hypergraph embedding is stabilised, send:
* markers 0,1,2 to themselves;
* every leaf to its image under the genuinely increasing composite;
* every 1-split to the target singleton meet of its chosen witnesses;
* every 2-split to the target full pair meet of its chosen witnesses.

The verified I2/I3 results imply the choices have the correct
predecessor interval and do not depend on the witnessing tuple.
The abstract interval lemma then proves the entire resulting map
is strictly increasing.

This is the candidate map and its local meet behaviour, not yet
the full diary pre-embedding: preservation of all leaf-pair meet
cases, the marker-1 orientation and flips remain separate.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph
open Ordered3Graph.UnorderedEmbedding

/-- Genuine leaves witnessing a singleton type split i. -/
structure OneSplitLeafWitness (H : Ordered3Graph Nat) (i : Nat) where
  u : Nat
  v : Nat
  hu : IsLeaf H u
  hv : IsLeaf H v
  hiu : i < u
  hiv : i < v
  meet_eq : H.oneMeetLevel u v = i

/-- Genuine ordered leaf pairs witnessing a full pair-type split i. -/
structure TwoSplitLeafPairWitness (H : Ordered3Graph Nat) (i : Nat) where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  hab : a < b
  hcd : c < d
  ha : IsLeaf H a
  hb : IsLeaf H b
  hc : IsLeaf H c
  hd : IsLeaf H d
  hia : i < a
  hic : i < c
  meet_eq : H.twoMeetLevel a b c d = i

namespace RoleDiary

variable {H : Ordered3Graph Nat}

/-- Choose one actual source witness for every 1-split,
using exactly V1 of RoleDiary. -/
noncomputable def chosenOneSplitWitness
    (D : RoleDiary H) (i : Nat) (hi : IsOneSplit H i) :
    OneSplitLeafWitness H i := by
  classical
  have hw : Nonempty (OneSplitLeafWitness H i) := by
    obtain ⟨u, v, hu, hv, hiu, hiv, hmeet⟩ :=
      D.one_split_witness i hi
    exact ⟨⟨u, v, hu, hv, hiu, hiv, hmeet⟩⟩
  exact Classical.choice hw

/-- Choose one actual source witness for every 2-split,
using exactly V2 of RoleDiary. -/
noncomputable def chosenTwoSplitWitness
    (D : RoleDiary H) (i : Nat) (hi : IsTwoSplit H i) :
    TwoSplitLeafPairWitness H i := by
  classical
  have hw : Nonempty (TwoSplitLeafPairWitness H i) := by
    obtain ⟨a, b, c, d, hab, hcd, ha, hb, hc, hd,
      hia, hic, hmeet⟩ := D.two_split_witness i hi
    exact ⟨⟨a, b, c, d, hab, hcd, ha, hb, hc, hd,
      hia, hic, hmeet⟩⟩
  exact Classical.choice hw

/-- The proposed image of a source 1-split is the full target
singleton meet of one chosen genuine leaf witness. -/
noncomputable def oneSplitTargetImage
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (D : RoleDiary H) (ψ : Embedding H G.graph)
    (i : Nat) (hi : IsOneSplit H i) : Nat :=
  let w := D.chosenOneSplitWitness i hi
  K.oneMeetLevel
    (stabilisedSource G K F ψ w.u)
    (stabilisedSource G K F ψ w.v)

/-- The proposed image of a source 2-split is the full target
pair-type meet of one chosen genuine pair-of-pairs witness. -/
noncomputable def twoSplitTargetImage
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (D : RoleDiary H) (ψ : Embedding H G.graph)
    (i : Nat) (hi : IsTwoSplit H i) : Nat :=
  let w := D.chosenTwoSplitWitness i hi
  K.twoMeetLevel
    (stabilisedSource G K F ψ w.a)
    (stabilisedSource G K F ψ w.b)
    (stabilisedSource G K F ψ w.c)
    (stabilisedSource G K F ψ w.d)

/-- The chosen one-split image belongs to the exact predecessor
interval of the stabilised leaf map; no gap preservation is assumed. -/
theorem oneSplitTargetImage_interval
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (D : RoleDiary H)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (i : Nat) (hi : IsOneSplit H i) :
    let φ := stabilisedSource G K F ψ
    φ (i-1) < D.oneSplitTargetImage G K F ψ i hi ∧
      D.oneSplitTargetImage G K F ψ i hi ≤ φ i := by
  let w := D.chosenOneSplitWitness i hi
  exact stabilisedSource_oneSplit_target_placement
    G K F ψ hψ i w.u w.v
    (by have hb := hi.1; omega)
    w.hiu w.hiv w.meet_eq

/-- The chosen two-split image belongs to the exact predecessor
interval of the stabilised leaf map. -/
theorem twoSplitTargetImage_interval
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (D : RoleDiary H)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (i : Nat) (hi : IsTwoSplit H i) :
    let φ := stabilisedSource G K F ψ
    φ (i-1) < D.twoSplitTargetImage G K F ψ i hi ∧
      D.twoSplitTargetImage G K F ψ i hi ≤ φ i := by
  let w := D.chosenTwoSplitWitness i hi
  exact stabilisedSource_twoSplit_target_placement
    G K F D ψ hψ i w.a w.b w.c w.d
    (by have hb := hi.1; omega)
    w.hia w.hic w.hab w.hcd
    w.ha w.hb w.hc w.hd w.meet_eq

/-- An arbitrary leaf witness of the same 1-split computes the
same image as the canonical chosen witness. This uses the complete
gappy-source I2 transfer and diary V/E/S classes, not a choice axiom. -/
theorem oneSplitTargetImage_eq_any_witness
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (D : RoleDiary H)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (i u v : Nat) (hi : IsOneSplit H i)
    (hu : IsLeaf H u) (hv : IsLeaf H v)
    (hiu : i < u) (hiv : i < v)
    (hmeet : H.oneMeetLevel u v = i) :
    D.oneSplitTargetImage G K F ψ i hi =
      K.oneMeetLevel
        (stabilisedSource G K F ψ u)
        (stabilisedSource G K F ψ v) := by
  let w := D.chosenOneSplitWitness i hi
  have heq := stabilisedSource_oneSplit_witness_independent
    G K F D ψ hψ i w.u w.v u v hi
    w.hu w.hv hu hv w.hiu w.hiv hiu hiv
    w.meet_eq hmeet
  exact heq.symm

/-- An arbitrary ordered pair-of-pairs witness of the same 2-split
computes exactly the chosen target full pair meet. -/
theorem twoSplitTargetImage_eq_any_witness
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (D : RoleDiary H)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (i a b c d : Nat) (hi : IsTwoSplit H i)
    (hia : i < a) (hic : i < c)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hmeet : H.twoMeetLevel a b c d = i) :
    D.twoSplitTargetImage G K F ψ i hi =
      K.twoMeetLevel
        (stabilisedSource G K F ψ a)
        (stabilisedSource G K F ψ b)
        (stabilisedSource G K F ψ c)
        (stabilisedSource G K F ψ d) := by
  let w := D.chosenTwoSplitWitness i hi
  have heq := stabilisedSource_twoSplit_all_witnesses
    G K F D ψ hψ i w.a w.b w.c w.d a b c d hi
    w.hia w.hic hia hic w.hab w.hcd hab hcd
    w.ha w.hb w.hc w.hd ha hb hc hd
    w.meet_eq hmeet
  exact heq.symm

/-- The actual proposed total diary map: fixed markers,
actual target images on leaves, and the chosen target type meet
for each 1-split or 2-split. Its definition uses NO arbitrary
target meet-preservation assumption. -/
noncomputable def chosenPreembedding
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (D : RoleDiary H) (ψ : Embedding H G.graph)
    (i : Nat) : Nat := by
  classical
  exact
    if hsmall : i < 3 then i
    else if hleaf : IsLeaf H i then stabilisedSource G K F ψ i
    else if hone : IsOneSplit H i then
      D.oneSplitTargetImage G K F ψ i hone
    else
      D.twoSplitTargetImage G K F ψ i (by
        have hi : 3 ≤ i := by omega
        rcases D.role_valid i hi with hl | ho | ht
        · exact False.elim (hleaf hl)
        · exact False.elim (hone ho)
        · exact ht)

/-- Markers are fixed pointwise. -/
theorem chosenPreembedding_zero
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (D : RoleDiary H) (ψ : Embedding H G.graph) :
    D.chosenPreembedding G K F ψ 0 = 0 := by
  simp [chosenPreembedding]

theorem chosenPreembedding_one
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (D : RoleDiary H) (ψ : Embedding H G.graph) :
    D.chosenPreembedding G K F ψ 1 = 1 := by
  simp [chosenPreembedding]

theorem chosenPreembedding_two
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (D : RoleDiary H) (ψ : Embedding H G.graph) :
    D.chosenPreembedding G K F ψ 2 = 2 := by
  simp [chosenPreembedding]

/-- On actual leaves, the proposed map is precisely the
stabilised increasing induced hypergraph embedding. -/
theorem chosenPreembedding_leaf
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (D : RoleDiary H) (ψ : Embedding H G.graph)
    (i : Nat) (hi : IsLeaf H i) :
    D.chosenPreembedding G K F ψ i = stabilisedSource G K F ψ i := by
  have hbound : ¬ i < 3 := by have h := hi.1; omega
  simp [chosenPreembedding, hbound, hi]

theorem chosenPreembedding_oneSplit
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (D : RoleDiary H) (ψ : Embedding H G.graph)
    (i : Nat) (hi : IsOneSplit H i) :
    D.chosenPreembedding G K F ψ i =
      D.oneSplitTargetImage G K F ψ i hi := by
  have hbound : ¬ i < 3 := by have h := hi.1; omega
  have hnotLeaf : ¬ IsLeaf H i := by
    intro h
    exact h.2.1 hi.2.1
  simp [chosenPreembedding, hbound, hnotLeaf, hi]

theorem chosenPreembedding_twoSplit
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (D : RoleDiary H) (ψ : Embedding H G.graph)
    (i : Nat) (hi : IsTwoSplit H i) :
    D.chosenPreembedding G K F ψ i =
      D.twoSplitTargetImage G K F ψ i hi := by
  have hbound : ¬ i < 3 := by have h := hi.1; omega
  have hnotLeaf : ¬ IsLeaf H i := by
    intro h
    exact h.2.2 hi.2.2
  have hnotOne : ¬ IsOneSplit H i := by
    intro h
    exact hi.2.1 h.2.1
  simp [chosenPreembedding, hbound, hnotLeaf, hnotOne]

/-- The TOTAL chosen diary pre-embedding candidate is strictly
increasing. This follows from the genuine local split placement
intervals and the role partition, with no global meet-preservation
or role compatibility of the target asserted at this stage. -/
theorem chosenPreembedding_strictMono
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (D : RoleDiary H)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting) :
    StrictMono (D.chosenPreembedding G K F ψ) := by
  let φ := stabilisedSource G K F ψ
  apply strictMono_of_diary_role_intervals
    D φ (D.chosenPreembedding G K F ψ) φ.strictMono
    (D.chosenPreembedding_zero G K F ψ)
    (D.chosenPreembedding_one G K F ψ)
    (D.chosenPreembedding_two G K F ψ)
  · intro i _ hi
    exact D.chosenPreembedding_leaf G K F ψ i hi
  · intro i hi
    rw [D.chosenPreembedding_oneSplit G K F ψ i hi]
    exact D.oneSplitTargetImage_interval G K F ψ hψ i hi
  · intro i hi
    rw [D.chosenPreembedding_twoSplit G K F ψ i hi]
    exact D.twoSplitTargetImage_interval G K F ψ hψ i hi

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
