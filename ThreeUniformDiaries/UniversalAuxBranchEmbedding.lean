import ThreeUniformDiaries.FixedPrefixBranchAuxEmbedding
import ThreeUniformDiaries.RootBranchAuxEmbedding
import ThreeUniformDiaries.ExactMeetsFromTypes

/-!
# One K_I embedding valid simultaneously for every canonical branch

For each prescribed I = G|n, a single length-first presentation E of K_I
and a single global embedding phi : E.graph -> G can be chosen so that
for **every** H extending I, the branch map composed with phi is an
aux-type-respecting induced embedding fixing n. We choose the root-based
construction for n=0 and the inherited fixed-prefix construction for n>0.

This verifies the mathematical core of Lemma Kiemb in the indexed K_I
presentation. It does not supply the strong-tree coding or the Ramsey
theorem which uses Kiemb.
-/

namespace ThreeUniformDiaries

/-- The uniform conclusion required of the generic K_I embedding. -/
def UniversalAuxBranchProperty
    (G : GenericEnumerated3Graph) {n : Nat}
    (I : EnumNode n)
    (E : SizeFirstBranchPresentation I)
    (phi : Nat → Nat) : Prop :=
  StrictMono phi ∧
  (∀ k : Nat, k < n → phi k = k) ∧
  (∀ a b c : Nat, a < b → b < c →
    (E.graph.edge a b c ↔
      G.graph.edge (phi a) (phi b) (phi c))) ∧
  ∀ (H : Ordered3Graph Nat) (hI : H.initialSegment n = I),
    ∃ e : Ordered3Graph.Embedding H G.graph,
      (∀ v : Nat, e v = phi (E.branchIndex H hI v)) ∧
      (∀ k : Nat, k < n → e k = k) ∧
      e.AuxTypeRespecting

/-- For a nonempty fixed I, construct the global K_I embedding once,
not separately for each H extending I. -/
theorem exists_universal_fixedAuxEmbedding
    (G : GenericEnumerated3Graph) {n : Nat}
    (I : EnumNode n) (hn : 0 < n)
    (hGI : G.graph.initialSegment n = I) :
    ∃ E : SizeFirstBranchPresentation I, ∃ phi : Nat → Nat,
      UniversalAuxBranchProperty G I E phi := by
  let E : SizeFirstBranchPresentation I :=
    canonicalSizeFirstBranchPresentation I
  have hKG : E.graph.initialSegment n = G.graph.initialSegment n :=
    (E.graph_initialSegment_eq G.graph hGI).trans hGI.symm
  let parent := E.fixedSourceParents hn
  let phi := G.fixedInheritedEmbedding E.graph n hKG parent
  have hp := G.fixedInheritedEmbedding_isEmbedding E.graph n hKG parent
  refine ⟨E, phi, hp.1, hp.2.1, hp.2.2, ?_⟩
  intro H hH
  let e := E.fixedBranchEmbedding G hKG hn H hH
  refine ⟨e, ?_, ?_, E.fixedBranch_auxTypeRespecting G hKG hn H hH⟩
  · intro v
    rfl
  · intro k hk
    exact E.fixedBranchEmbedding_prefix G hKG hn H hH k hk

/-- The root-based construction supplies the remaining case n=0. -/
theorem exists_universal_zeroAuxEmbedding
    (G : GenericEnumerated3Graph)
    (I : EnumNode 0) :
    ∃ E : SizeFirstBranchPresentation I, ∃ phi : Nat → Nat,
      UniversalAuxBranchProperty G I E phi := by
  let E : SizeFirstBranchPresentation I :=
    canonicalSizeFirstBranchPresentation I
  let phi := G.inheritedEmbedding E.graph E.sourceParentSchedule
  have hp := G.exists_countable_inherited_embedding
    E.graph E.sourceParentSchedule
  refine ⟨E, phi, hp.1, ?_, hp.2, ?_⟩
  · intro k hk
    omega
  · intro H hH
    let e := E.rootBranchEmbedding G H hH
    refine ⟨e, ?_, ?_, E.rootBranch_auxTypeRespecting G H hH⟩
    · intro v
      rfl
    · intro k hk
      omega

/-- Uniform K_I embedding for every finite prescribed initial segment,
including n=0: one phi works for *all* H extending I. -/
theorem exists_universal_auxEmbedding
    (G : GenericEnumerated3Graph) {n : Nat}
    (I : EnumNode n)
    (hGI : G.graph.initialSegment n = I) :
    ∃ E : SizeFirstBranchPresentation I, ∃ phi : Nat → Nat,
      UniversalAuxBranchProperty G I E phi := by
  by_cases hn : 0 < n
  · exact exists_universal_fixedAuxEmbedding G I hn hGI
  · have hz : n = 0 := by omega
    subst n
    exact exists_universal_zeroAuxEmbedding G I

/-- Consequently every canonical H branch preserves literal capped
singleton and auxiliary meets, uniformly for the same global phi. -/
theorem exists_universal_exactMeetEmbedding
    (G : GenericEnumerated3Graph) {n : Nat}
    (I : EnumNode n)
    (hGI : G.graph.initialSegment n = I) :
    ∃ E : SizeFirstBranchPresentation I, ∃ phi : Nat → Nat,
      UniversalAuxBranchProperty G I E phi ∧
      ∀ (H : Ordered3Graph Nat) (hI : H.initialSegment n = I),
        ∃ e : Ordered3Graph.Embedding H G.graph,
          (∀ v : Nat, e v = phi (E.branchIndex H hI v)) ∧
          (∀ u v : Nat,
            G.graph.oneMeetLevel (e u) (e v) =
              e (H.oneMeetLevel u v)) ∧
          (∀ u₀ u₁ v₀ v₁ : Nat, u₀ < u₁ → v₀ < v₁ →
            G.graph.auxMeetLevel (e u₀) (e u₁) (e v₀) (e v₁) =
              e (H.auxMeetLevel u₀ u₁ v₀ v₁)) := by
  obtain ⟨E, phi, hphi⟩ :=
    exists_universal_auxEmbedding G I hGI
  refine ⟨E, phi, hphi, ?_⟩
  intro H hH
  obtain ⟨e, he, _, haux⟩ := hphi.2.2.2 H hH
  refine ⟨e, he, ?_, ?_⟩
  · intro u v
    exact e.oneMeetLevel_eq_of_auxTypeRespecting haux u v
  · intro u₀ u₁ v₀ v₁ hu hv
    exact e.auxMeetLevel_eq_of_auxTypeRespecting haux
      u₀ u₁ v₀ v₁ hu hv

end ThreeUniformDiaries
