import ThreeUniformDiaries.DiaryFusedLeafPairs
import ThreeUniformDiaries.DiaryUnorderedNativeStabilisation
import ThreeUniformDiaries.DiaryPreembeddingTwoSplit
import ThreeUniformDiaries.DiaryPreembeddingTwoSplitPlacement

/-!
# Genuine diary-source I3 and full two-split pre-embedding intervals

The native fused I3 theorem compares finite pointed ATR sources at a
cut in the generic enumeration. A type-respecting source embedding
ψ : D → G can skip levels. The manuscript requires comparison at
the image of the PREDECESSOR diary index; this module restricts the
already established native equality to that genuinely smaller cut.

An arbitrary unordered outside hypergraph embedding is allowed:
the induced ordered copy is the verified fused embedding followed
by the original diary-to-generic map. We then derive the placement
of an actual diary 2-split and invariance under replacing its
witnessing pairs. The final invariance lemma explicitly assumes
the witnesses are equivalent through the successor diary cut;
deriving that equivalence from the diary role axioms is separate.

No global preservation of full type meets through skipped levels
is postulated.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph
namespace UnorderedEmbedding

/-- The ordered induced image of an original diary source in the
stabilised generic copy. The original outer embedding remains
unordered; only the checked fused composite is increasing. -/
noncomputable def stabilisedSource
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    {H : Ordered3Graph Nat}
    (ψ : Embedding H G.graph) : Embedding H K where
  toFun := fun t => stabilisedOrdered G K F (ψ t)
  strictMono := (stabilisedOrdered G K F).strictMono.comp ψ.strictMono
  edge_iff := by
    intro a b c hab hbc
    exact (ψ.edge_iff hab hbc).trans
      ((stabilisedOrdered G K F).edge_iff
        (ψ.strictMono hab) (ψ.strictMono hbc))

/-- Full I3 for actual pairs of diary leaves at the predecessor
DIARY cut rather than the predecessor of its (possibly gappy)
generic image. Lexicographic orientation is unaffected by
restriction. This does not assume the initial outer map is ordered. -/
theorem stabilisedSource_diaryLeafPairType_orientation
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    {H : Ordered3Graph Nat}
    (D : DiaryLeafPriority.RoleDiary H)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (i a b c d : Nat) (hi : 3 ≤ i)
    (hia : i ≤ a) (hic : i ≤ c)
    (hab : a < b) (hcd : c < d)
    (ha : DiaryLeafPriority.IsLeaf H a)
    (hb : DiaryLeafPriority.IsLeaf H b)
    (hc : DiaryLeafPriority.IsLeaf H c)
    (hd : DiaryLeafPriority.IsLeaf H d)
    (hpair : H.SameTwoTypeBelow i a b c d) :
    let φ := stabilisedSource G K F ψ
    K.SameTwoTypeBelow (φ (i-1)+1)
      (φ a) (φ b) (φ c) (φ d) ∧
    (DiaryLeafPriority.LexEarlier K (φ a) (φ b) ↔
     DiaryLeafPriority.LexEarlier K (φ c) (φ d)) := by
  let Φ := stabilisedOrdered G K F
  have hnative := ATRFiniteDecoder.orderedDiaryFusion_diaryLeafPairType_orientation
    G K F.toFun F.injective D ψ hψ i a b c d hi
    hia hic hab hcd ha hb hc hd hpair
  change K.SameTwoTypeBelow (Φ (ψ i-1)+1)
      (Φ (ψ a)) (Φ (ψ b)) (Φ (ψ c)) (Φ (ψ d)) ∧
    (DiaryLeafPriority.LexEarlier K (Φ (ψ a)) (Φ (ψ b)) ↔
     DiaryLeafPriority.LexEarlier K (Φ (ψ c)) (Φ (ψ d))) at hnative
  have hpre : i-1 < i := by omega
  have hψpre : ψ (i-1) < ψ i := ψ.strictMono hpre
  have hψcut : ψ (i-1) ≤ ψ i-1 := by omega
  have hcut : Φ (ψ (i-1))+1 ≤ Φ (ψ i-1)+1 := by
    have hmono : Φ (ψ (i-1)) ≤ Φ (ψ i-1) :=
      Φ.strictMono.monotone hψcut
    omega
  have hsmall : K.SameTwoTypeBelow (Φ (ψ (i-1))+1)
      (Φ (ψ a)) (Φ (ψ b)) (Φ (ψ c)) (Φ (ψ d)) :=
    K.sameTwoTypeBelow_mono
      (Φ (ψ (i-1))+1) (Φ (ψ i-1)+1)
      (Φ (ψ a)) (Φ (ψ b)) (Φ (ψ c)) (Φ (ψ d))
      hcut hnative.1
  exact ⟨hsmall, hnative.2⟩

/-- The complete 2-type of two source pairs with first disagreement
at a genuine 2-split i becomes a target meet inside exactly the
predecessor interval (φ(i-1), φ(i)]. I3 supplies the lower bound,
while induced edge REFLECTION at the actual image of i supplies
the upper bound, even with arbitrary omitted levels. -/
theorem stabilisedSource_twoSplit_target_placement
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    {H : Ordered3Graph Nat}
    (D : DiaryLeafPriority.RoleDiary H)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (i a b c d : Nat) (hi : 3 ≤ i)
    (hia : i < a) (hic : i < c)
    (hab : a < b) (hcd : c < d)
    (ha : DiaryLeafPriority.IsLeaf H a)
    (hb : DiaryLeafPriority.IsLeaf H b)
    (hc : DiaryLeafPriority.IsLeaf H c)
    (hd : DiaryLeafPriority.IsLeaf H d)
    (hmeet : H.twoMeetLevel a b c d = i) :
    let φ := stabilisedSource G K F ψ
    φ (i-1) < K.twoMeetLevel (φ a) (φ b) (φ c) (φ d) ∧
    K.twoMeetLevel (φ a) (φ b) (φ c) (φ d) ≤ φ i := by
  let φ := stabilisedSource G K F ψ
  have hpair : H.SameTwoTypeBelow i a b c d := by
    simpa only [hmeet] using H.twoMeetLevel_agree a b c d
  have htarget : K.SameTwoTypeBelow (φ (i-1)+1)
      (φ a) (φ b) (φ c) (φ d) :=
    (stabilisedSource_diaryLeafPairType_orientation
      G K F D ψ hψ i a b c d hi
      (by omega) (by omega) hab hcd ha hb hc hd hpair).1
  exact twoSplit_target_placement φ i a b c d
    (by omega) hia hab hic hcd hmeet htarget

/-- Replacing both pairs of leaves witnessing the same full
2-split preserves its target meet. The source type hypotheses at
i+1 record exactly the two witness classes required by I3. -/
theorem stabilisedSource_twoSplit_witness_independent
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    {H : Ordered3Graph Nat}
    (D : DiaryLeafPriority.RoleDiary H)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (i a b c d a' b' c' d' : Nat) (hi : 3 ≤ i)
    (hia : i < a) (hic : i < c)
    (hia' : i < a') (hic' : i < c')
    (hab : a < b) (hcd : c < d)
    (hab' : a' < b') (hcd' : c' < d')
    (ha : DiaryLeafPriority.IsLeaf H a)
    (hb : DiaryLeafPriority.IsLeaf H b)
    (hc : DiaryLeafPriority.IsLeaf H c)
    (hd : DiaryLeafPriority.IsLeaf H d)
    (ha' : DiaryLeafPriority.IsLeaf H a')
    (hb' : DiaryLeafPriority.IsLeaf H b')
    (hc' : DiaryLeafPriority.IsLeaf H c')
    (hd' : DiaryLeafPriority.IsLeaf H d')
    (hmeet : H.twoMeetLevel a b c d = i)
    (hSameA : H.SameTwoTypeBelow (i+1) a b a' b')
    (hSameB : H.SameTwoTypeBelow (i+1) c d c' d') :
    let φ := stabilisedSource G K F ψ
    K.twoMeetLevel (φ a') (φ b') (φ c') (φ d') =
      K.twoMeetLevel (φ a) (φ b) (φ c) (φ d) := by
  let φ := stabilisedSource G K F ψ
  have hPlace := stabilisedSource_twoSplit_target_placement
    G K F D ψ hψ i a b c d hi hia hic hab hcd
    ha hb hc hd hmeet
  have hPrev : i+1-1 = i := by omega
  have hImageA : K.SameTwoTypeBelow (φ i+1)
      (φ a) (φ b) (φ a') (φ b') := by
    have h := (stabilisedSource_diaryLeafPairType_orientation
      G K F D ψ hψ (i+1) a b a' b' (by omega)
      (by omega) (by omega) hab hab' ha hb ha' hb' hSameA).1
    simpa only [hPrev] using h
  have hImageB : K.SameTwoTypeBelow (φ i+1)
      (φ c) (φ d) (φ c') (φ d') := by
    have h := (stabilisedSource_diaryLeafPairType_orientation
      G K F D ψ hψ (i+1) c d c' d' (by omega)
      (by omega) (by omega) hcd hcd' hc hd hc' hd' hSameB).1
    simpa only [hPrev] using h
  exact K.twoMeetLevel_pairWitness_independent
    (φ i) (φ a) (φ b) (φ c) (φ d)
    (φ a') (φ b') (φ c') (φ d')
    (φ.strictMono hia) (φ.strictMono hic)
    (φ.strictMono hia') (φ.strictMono hic')
    hImageA hImageB hPlace.2

end UnorderedEmbedding
end Ordered3Graph
end ThreeUniformDiaries
