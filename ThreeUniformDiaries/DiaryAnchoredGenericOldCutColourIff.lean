import ThreeUniformDiaries.DiaryGenericGoodOrBadColourCone
import ThreeUniformDiaries.DiaryGenericMixedConeIndivisibility

/-!
# Track A: exact anchored generic old-cut colour criterion for whole reserved cones

English-first adversarial proof: janhubicka/3-uniform-diaries PR #331.

Fix a genuine new SOURCE leaf m and one OLD supported map f, with
the literal complete colour at oldStageTailCut H m f. Arbitrarily
late whole unordered induced generic target subcopies consisting of
ACTUAL compatible reserved immediate successor images exist IFF
SOME old-cut colour has BOTH:
  (a) an ACTUAL compatible reserved successor anchor anywhere in F;
  (b) an induced generic monochromatic true-leaf subcopy in the
      original prescribed target F range.

This does NOT assert such a colour exists. In particular, a
cofinally inhabited good colour need not be generically rich, and
generic finite-colour Ramsey refinement can choose a bad colour.

The forward direction uses the checked all-or-none reserved
old-colour theorem plus a generic empty-E5-pattern refinement.
The reverse direction monochromatizes one actual whole-good
generic copy using the checked finite singleton vertex-colour
generic Ramsey theorem, and verifies the induced composition.

No full RoleDiary source/target assumption and no target-monotone
outer embedding is used. No later-horizon persistent image follows.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- EXACT equivalence between whole cofinally-high generic copies of
compatible RESERVED next leaves and nonempty intersection of the
finite full-old-cut anchored and generically rich colour spectra.

Generic richness here means ONE ACTUAL unordered induced generic
subcopy wholly of colour c, with all vertices genuine leaves in
the ORIGINAL prescribed target F-range. Anchor means a genuine
full reserved next-leaf stage (including FutureOrderReserve),
not a bare finite generator candidate.

The source next leaf m must be genuine; f is arbitrary and is
automatically certified on the old support by any actual anchor.
The theorem does not prove a good generic colour exists. -/
theorem whole_reserved_nextLeaf_generic_cones_iff_anchored_generic_oldCut_colour
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (hm : IsLeaf H m)
    (G : GenericEnumerated3Graph) :
    (∃ c : Fin (oldStageTailCut H m f) →
        Fin (oldStageTailCut H m f) → Bool,
      ∃ J : Ordered3Graph.UnorderedEmbedding G.graph K,
        (∀ t : Nat,
          IsLeaf K (J t) ∧
          (∃ i : Nat, J t = F i) ∧
          DiaryLowerBoundColors.singletonColour K
            (oldStageTailCut H m f) (J t) = c) ∧
        (∃ v : Nat,
          HasCompatibleReservedNextLeaf H K F f m v ∧
          DiaryLowerBoundColors.singletonColour K
            (oldStageTailCut H m f) v = c)) ↔
    (∀ M : Nat,
      ∃ U : Ordered3Graph.UnorderedEmbedding G.graph K,
        ∀ n : Nat,
          M < U n ∧
          IsLeaf K (U n) ∧
          (∃ i : Nat, U n = F i) ∧
          HasCompatibleReservedNextLeaf H K F f m (U n)) := by
  classical
  constructor
  · rintro ⟨c, J, hJ, v, hAnchor, hAnchorColour⟩
    have hJLeaf (t : Nat) : IsLeaf K (J t) :=
      (hJ t).1
    have hJInF (t : Nat) : ∃ i : Nat, J t = F i :=
      (hJ t).2.1
    have hJColour (t : Nat) :
        DiaryLowerBoundColors.singletonColour K
          (oldStageTailCut H m f) (J t) = c :=
      (hJ t).2.2
    rcases exists_good_generic_cones_or_no_compatible_anchor_in_colour
      G J hJLeaf hJInF hm c hJColour with hNone | hGood
    · exact False.elim ((hNone v hAnchor) hAnchorColour)
    · exact hGood
  · intro hCones
    obtain ⟨U, hU⟩ := hCones 0
    let Cut := oldStageTailCut H m f
    obtain ⟨u, hu, c, hColour⟩ :=
      exists_generic_selfcopy_in_one_mixed_singleton_cone
        G K Cut (fun t : Nat => U t)
    let J : Ordered3Graph.UnorderedEmbedding G.graph K := {
      toFun := fun t => U (u t)
      injective := U.injective.comp u.strictMono.injective
      edge_iff := by
        intro a b d hab hbd
        calc
          G.graph.unorderedEdge a b d ↔ G.graph.edge a b d :=
            G.graph.unorderedEdge_iff_of_lt a b d hab hbd
          _ ↔ G.graph.edge (u a) (u b) (u d) :=
            u.edge_iff hab hbd
          _ ↔ G.graph.unorderedEdge (u a) (u b) (u d) :=
            (G.graph.unorderedEdge_iff_of_lt
              (u a) (u b) (u d)
              (u.strictMono hab) (u.strictMono hbd)).symm
          _ ↔ K.unorderedEdge (U (u a)) (U (u b)) (U (u d)) :=
            U.edge_iff (u a) (u b) (u d)
              (u.strictMono hab) (u.strictMono hbd)
    }
    refine ⟨c, J, ?_, J 0, ?_, ?_⟩
    · intro t
      obtain ⟨_hHigh, hLeaf, hAtF, _hGood⟩ := hU (u t)
      exact ⟨hLeaf, hAtF, hColour t⟩
    · exact (hU (u 0)).2.2.2
    · exact hColour 0

end DiaryLeafPriority
end ThreeUniformDiaries
