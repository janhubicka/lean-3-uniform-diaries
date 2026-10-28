import ThreeUniformDiaries.DiaryFiniteCanonicalCausalFullSourceEmbedding
import ThreeUniformDiaries.DiaryFiniteFamilyCountableCompletion

/-!
# A common countable diary with full embeddings of all canonical source flips

Every canonical SOURCE flip is an induced full numerical-meet copy of
the actual causal finite V/E pre-diary. The previously verified
FiniteMeetEmbedding.through_countable_completion theorem carries
each such finite embedding through ANY one common dummy-tail
prediary and its one-pass completion.

Choose the dummy-tail prediary ONCE, independently of the flip
index. Every source branch then embeds into the same countable
RoleDiary with all FiniteMeetEmbedding fields: strict order,
markers, all source roles, edges AND nonedges, singleton and full
ordered-pair numerical meets including mixed split/leaf cases.

This does not give a finite diary absorber or assert that EVERY
genuine flip of a fixed finite target contains the unflipped source.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- One common dummy-tail carrier for all canonical source flips. -/
noncomputable def canonicalCausalCountableCarrier
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n) (bits : Nat → Bool) :
    Ordered3Graph Nat :=
  finiteDummyTailCarrier
    (finiteCanonicalCausalMarkerGraph DA)
    (Fintype.card (FiniteCanonicalSignRootedVertex DA)) bits

/-- The complete concrete source-to-countable vertex map. -/
noncomputable def canonicalCausalCountableSourceMap
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n) (bits : Nat → Bool)
    (i : FiniteCanonicalFlipIndex A n) (u : Nat) : Nat :=
  onePassOldImage (canonicalCausalCountableCarrier DA bits)
    (finiteCanonicalSourceRankMap DA i u)

/-- Strong simultaneous source-orbit embedding theorem.

One choice of countable RoleDiary works for EVERY genuine canonical
source flip, and every induced finite-meet embedding has ALL of its
structure fields checked. The source flip itself, not the original
unflipped source, is the embedded finite structure. -/
theorem exists_countableDiary_simultaneousCanonicalSourceFlips_fullEmbedding
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n) :
    ∃ bits : Nat → Bool,
      RoleDiary
        (onePassRawTarget (canonicalCausalCountableCarrier DA bits)) ∧
      (∀ i : FiniteCanonicalFlipIndex A n,
        FiniteMeetEmbedding
          ((finiteCanonicalSignRootedFamily DA).graph i)
          (onePassRawTarget (canonicalCausalCountableCarrier DA bits))
          n (canonicalCausalCountableSourceMap DA bits i)) := by
  let F := finiteCanonicalSignRootedFamily DA
  let G := finiteCanonicalCausalMarkerGraph DA
  let N := Fintype.card (FiniteCanonicalSignRootedVertex DA)
  have PG : FiniteRolePrediaryBlock G N :=
    finiteCanonicalCausalMarkerGraph_finitePrediary DA
  obtain ⟨bits,PT⟩ := exists_finiteDummyTailCarrier_prediary PG
  refine ⟨bits, onePassRawTarget_isDiary PT, ?_⟩
  intro i
  have E : FiniteMeetEmbedding (F.graph i) G n
      (finiteCanonicalSourceRankMap DA i) :=
    finiteCanonicalCausalMarkerGraph_sourceFiniteMeetEmbedding DA i
  have hRange : ∀ u : Nat, 3 ≤ u → u < n →
      finiteCanonicalSourceRankMap DA i u < N := by
    intro u _hun3 hun
    exact finiteCanonicalSourceRankMap_lt_carrier DA i u hun
  change FiniteMeetEmbedding (F.graph i)
    (onePassRawTarget (finiteDummyTailCarrier G N bits)) n
    (fun u => onePassOldImage (finiteDummyTailCarrier G N bits)
      (finiteCanonicalSourceRankMap DA i u))
  exact E.through_countable_completion PG
    (F.flip i).target_diary hRange bits PT

/-- The explicit edge and exact numerical-meet form of the stronger
common-countable-diary embedding theorem. All equations hold within
each individual source flip; no cross-branch equation is asserted. -/
theorem exists_countableDiary_simultaneousCanonicalSourceFlips
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n) :
    ∃ bits : Nat → Bool,
      RoleDiary
        (onePassRawTarget (canonicalCausalCountableCarrier DA bits)) ∧
      (∀ (i : FiniteCanonicalFlipIndex A n) (u v : Nat),
        3 ≤ u → u < n → 3 ≤ v → v < n →
        (onePassRawTarget (canonicalCausalCountableCarrier DA bits)).oneMeetLevel
          (canonicalCausalCountableSourceMap DA bits i u)
          (canonicalCausalCountableSourceMap DA bits i v) =
        canonicalCausalCountableSourceMap DA bits i
          (((finiteCanonicalSignRootedFamily DA).graph i).oneMeetLevel u v)) ∧
      (∀ (i : FiniteCanonicalFlipIndex A n) (a b c d : Nat),
        a < b → c < d →
        3 ≤ a → a < n → 3 ≤ b → b < n →
        3 ≤ c → c < n → 3 ≤ d → d < n →
        (onePassRawTarget (canonicalCausalCountableCarrier DA bits)).twoMeetLevel
          (canonicalCausalCountableSourceMap DA bits i a)
          (canonicalCausalCountableSourceMap DA bits i b)
          (canonicalCausalCountableSourceMap DA bits i c)
          (canonicalCausalCountableSourceMap DA bits i d) =
        canonicalCausalCountableSourceMap DA bits i
          (((finiteCanonicalSignRootedFamily DA).graph i).twoMeetLevel a b c d)) ∧
      (∀ (i : FiniteCanonicalFlipIndex A n) (a b c : Nat),
        a < b → b < c → c < n →
        ((onePassRawTarget (canonicalCausalCountableCarrier DA bits)).edge
          (canonicalCausalCountableSourceMap DA bits i a)
          (canonicalCausalCountableSourceMap DA bits i b)
          (canonicalCausalCountableSourceMap DA bits i c) ↔
          ((finiteCanonicalSignRootedFamily DA).graph i).edge a b c)) := by
  obtain ⟨bits,hD,hEmb⟩ :=
    exists_countableDiary_simultaneousCanonicalSourceFlips_fullEmbedding DA
  refine ⟨bits,hD,?_,?_,?_⟩
  · intro i u v hu3 hun hv3 hvn
    exact (hEmb i).oneMeet u v hu3 hun hv3 hvn
  · intro i a b c d hab hcd ha3 han hb3 hbn hc3 hcn hd3 hdn
    exact (hEmb i).twoMeet a b c d hab hcd
      ha3 han hb3 hbn hc3 hcn hd3 hdn
  · intro i a b c hab hbc hcn
    exact (hEmb i).edge_iff a b c hab hbc hcn

end DiaryLeafPriority
end ThreeUniformDiaries
