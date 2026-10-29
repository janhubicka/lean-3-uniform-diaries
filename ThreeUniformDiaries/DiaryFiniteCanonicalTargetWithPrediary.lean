import ThreeUniformDiaries.DiaryFiniteCanonicalCausalFullTarget

/-!
# An explicit finite full diary with the SAME dummy-tail V/E certificate

For geometric first-difference arguments it is essential to keep
the chosen dummy-tail bits together with the real RolePrediary
certificate used by the one-pass completion. The existential
finite canonical-orbit target theorem chooses such bits but hides
the V/E witness; reselecting independent bits could break
cross-copy meet transport.

We export the construction at ANY bits satisfying the actual
dummy-tail pre-diary condition. The target and all its canonical
source maps are EXACT concrete terms, and the full bounded
embedding certificates are supplied for the SAME chosen bits.
This is not a proof of target-flip absorption.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Given one real dummy-tail V/E pre-diary, the finite support
of all canonical source leaf images is a full finite diary,
and all canonical source flip embeddings into it are bounded.
The construction uses precisely the supplied bits, not a
separately chosen successful completion. -/
theorem canonicalCausalOrbitFiniteTarget_of_prediary
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n) (bits : Nat → Bool)
    (PT : RolePrediary (canonicalCausalCountableCarrier DA bits)) :
    FiniteRoleDiaryBlock
      (canonicalCausalOrbitFiniteTarget DA bits)
      (canonicalCausalOrbitFiniteSupport DA bits).card ∧
    (∀ i : FiniteCanonicalFlipIndex A n,
      FiniteBoundedMeetEmbedding
        ((finiteCanonicalSignRootedFamily DA).graph i)
        (canonicalCausalOrbitFiniteTarget DA bits)
        n (canonicalCausalOrbitFiniteSupport DA bits).card
        (canonicalCausalOrbitFiniteSourceMap DA bits i)) := by
  classical
  let F := finiteCanonicalSignRootedFamily DA
  let C := finiteCanonicalCausalMarkerGraph DA
  let N := Fintype.card (FiniteCanonicalSignRootedVertex DA)
  let H := canonicalCausalCountableCarrier DA bits
  let G := onePassRawTarget H
  let L := canonicalCausalOrbitFiniteLeaves DA bits
  let S := canonicalCausalOrbitFiniteSupport DA bits
  have PC : FiniteRolePrediaryBlock C N :=
    finiteCanonicalCausalMarkerGraph_finitePrediary DA
  have hDiary : RoleDiary G := onePassRawTarget_isDiary PT
  have hEmb (i : FiniteCanonicalFlipIndex A n) :
      FiniteMeetEmbedding (F.graph i) G n
        (canonicalCausalCountableSourceMap DA bits i) := by
    have E : FiniteMeetEmbedding (F.graph i) C n
        (finiteCanonicalSourceRankMap DA i) :=
      finiteCanonicalCausalMarkerGraph_sourceFiniteMeetEmbedding DA i
    have hRange : ∀ u : Nat, 3 ≤ u → u < n →
        finiteCanonicalSourceRankMap DA i u < N := by
      intro u _hu3 hun
      exact finiteCanonicalSourceRankMap_lt_carrier DA i u hun
    change FiniteMeetEmbedding (F.graph i)
      (onePassRawTarget (finiteDummyTailCarrier C N bits)) n
      (fun u => onePassOldImage (finiteDummyTailCarrier C N bits)
        (finiteCanonicalSourceRankMap DA i u))
    exact E.through_countable_completion PC
      (F.flip i).target_diary hRange bits PT
  have hLeaves : ∀ u : Nat, u ∈ L → IsLeaf G u :=
    canonicalCausalOrbitFiniteLeaves_areLeaves DA bits hEmb
  have hFull :
      FiniteRoleDiaryBlock (finiteSupportGraph G S) S.card :=
    finiteLeafMeetSupport_is_finiteDiary hDiary hLeaves
  refine ⟨hFull, ?_⟩
  intro i
  let f := canonicalCausalCountableSourceMap DA bits i
  have hSelected : ∀ u : Nat, 3 ≤ u → u < n →
      IsLeaf (F.graph i) u → f u ∈ L := by
    intro u hu3 hun hu
    exact canonicalCausalOrbitFiniteLeaves_mem DA bits i u hu3 hun hu
  have hRange : ∀ u : Nat, u < n → f u ∈ S :=
    (hEmb i).range_subset_leafMeetSupport
      (F.flip i).target_diary L hSelected
  have hFinite : FiniteMeetEmbedding
      (F.graph i) (finiteSupportGraph G S) n
      (finiteSupportLift S n f) :=
    (hEmb i).through_finiteSupport
      (F.flip i).target_diary S hRange
  refine ⟨hFinite, ?_⟩
  intro u hu
  exact (finiteSupportLift_spec S n f hRange u hu).1

/-- Choose the dummy-tail bits ONCE and expose the exact V/E
certificate alongside the final finite full target, preserving
the same source branch maps for geometric target-flip tests. -/
theorem exists_canonicalCausalOrbitFiniteTarget_with_prediary
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n) :
    ∃ bits : Nat → Bool,
      RolePrediary (canonicalCausalCountableCarrier DA bits) ∧
      FiniteRoleDiaryBlock
        (canonicalCausalOrbitFiniteTarget DA bits)
        (canonicalCausalOrbitFiniteSupport DA bits).card ∧
      (∀ i : FiniteCanonicalFlipIndex A n,
        FiniteBoundedMeetEmbedding
          ((finiteCanonicalSignRootedFamily DA).graph i)
          (canonicalCausalOrbitFiniteTarget DA bits)
          n (canonicalCausalOrbitFiniteSupport DA bits).card
          (canonicalCausalOrbitFiniteSourceMap DA bits i)) := by
  let C := finiteCanonicalCausalMarkerGraph DA
  let N := Fintype.card (FiniteCanonicalSignRootedVertex DA)
  have PC : FiniteRolePrediaryBlock C N :=
    finiteCanonicalCausalMarkerGraph_finitePrediary DA
  obtain ⟨bits,PT⟩ := exists_finiteDummyTailCarrier_prediary PC
  have h : FiniteRoleDiaryBlock
       (canonicalCausalOrbitFiniteTarget DA bits)
       (canonicalCausalOrbitFiniteSupport DA bits).card ∧
       (∀ i : FiniteCanonicalFlipIndex A n,
         FiniteBoundedMeetEmbedding
           ((finiteCanonicalSignRootedFamily DA).graph i)
           (canonicalCausalOrbitFiniteTarget DA bits)
           n (canonicalCausalOrbitFiniteSupport DA bits).card
           (canonicalCausalOrbitFiniteSourceMap DA bits i)) :=
    canonicalCausalOrbitFiniteTarget_of_prediary DA bits PT
  exact ⟨bits,PT,h.1,h.2⟩

end DiaryLeafPriority
end ThreeUniformDiaries
