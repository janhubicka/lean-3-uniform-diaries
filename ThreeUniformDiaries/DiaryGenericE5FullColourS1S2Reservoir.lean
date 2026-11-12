import ThreeUniformDiaries.DiaryUniformGenericFullColourS1S2
import ThreeUniformDiaries.DiaryGenericOldE5TargetLeafRange

/-!
# Track C: entire generic E5 fibres with cofinal uniform mixed/S1/S2 profiles

English proof/adversarial scope audit:
  janhubicka/3-uniform-diaries PR #306

The CI-verified Track C E5-fibre theorem produces an ACTUAL
induced generic target leaf subcopy J[G] inside the ORIGINAL
prescribed unordered generic leaf range, in which EVERY leaf
realizes a chosen finite positive/negative old-pair E5 pattern.

The strengthened finite-colour generic-subcopy theorem then
homogenizes, on ACTUAL induced generic subcopies of J[G], one
complete mixed singleton colour and all finite-root numerical
S1/S2 generator profiles. ONE profile triple is supported at
EVERY arbitrarily high target tail. Unlike a mere cofinally
recurrent set of individual leaves, each tail contains a whole
induced generic subcopy preserving all internal E5 triples
and nontriples.

The numeric profiles are selected existentially and are not
asserted to match any independently prescribed old source
diary stage; no reserved successor, E2/E3 relative table
realization, or countable unavoidability follows.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A cofinal induced generic reservoir inside an arbitrary
prescribed finite old E5-pattern fibre, whose true-leaf vertices
also share ONE complete mixed singleton colour and ONE finite
numerical S1/S2 rooted profile.

The actual generic subcopies exist beyond EVERY target numerical
cutoff B, with their selected profile triple fixed once and for
all. Both positive and negative E5 tests against old protected
vertices are preserved from the original J[G], and all new-internal
E5 tests are induced by J and its ordered generic selfembedding.

No source-requested numerical profile, old E2/E3 incidence table,
future reserve or persistent next-leaf image is asserted. -/
theorem RoleDiary.exists_uniform_generic_oldE5_fullColour_S1_S2_reservoir
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (A : Finset Nat) (theta : Nat → Nat → Bool)
    (W : Finset Nat) (hRoots : ∀ w : Nat, w ∈ W → IsLeaf K w)
    (Cut M : Nat) :
    ∃ J : Ordered3Graph.UnorderedEmbedding G.graph K,
      (∀ n : Nat, M < J n ∧ IsLeaf K (J n) ∧
        ∃ t : Nat, J n = F t) ∧
      (∀ n a : Nat, a ∈ A → F a < J n) ∧
      (∀ n a b : Nat, a ∈ A → b ∈ A → a < b →
        (K.unorderedEdge (F a) (F b) (J n) ↔ theta a b = true)) ∧
      ∃ c : Fin Cut → Fin Cut → Bool,
        ∃ p : FiniteRootMeetProfile W,
          ∃ q : FiniteRootCrossPairMeetProfile W,
            (∀ w : {w : Nat // w ∈ W},
              IsOneSplit K (p w).val ∧ (p w).val < w.val) ∧
            (∀ ab : {ab : Nat × Nat // ab ∈ finiteOrderedLeafPairs W},
              ∀ w : {w : Nat // w ∈ W},
                (q ab w).val = min ab.val.1 w.val ∨
                (q ab w).val = 1 ∨ IsTwoSplit K (q ab w).val) ∧
            (∀ B : Nat,
              ∃ (u : Ordered3Graph.Embedding G.graph G.graph),
                u.AuxTypeRespecting ∧
                ∀ t : Nat,
                  B < J (u t) ∧ IsLeaf K (J (u t)) ∧
                  DiaryLowerBoundColors.singletonColour K Cut (J (u t)) = c ∧
                  (∀ w : {w : Nat // w ∈ W},
                    K.oneMeetLevel w.val (J (u t)) = (p w).val) ∧
                  (∀ ab : {ab : Nat × Nat //
                      ab ∈ finiteOrderedLeafPairs W},
                    ∀ w : {w : Nat // w ∈ W},
                      K.twoMeetLevel ab.val.1 ab.val.2
                        w.val (J (u t)) = (q ab w).val)) := by
  obtain ⟨J, hRange, hAboveOld, hPattern⟩ :=
    exists_generic_leaf_subcopy_in_prescribed_oldE5_fibre
      G K F hFLeaf A theta M
  have hJLeaf : ∀ t : Nat, IsLeaf K (J t) := by
    intro t
    exact (hRange t).2.1
  obtain ⟨c, p, q, hOneRole, hTwoRole, hAll⟩ :=
    DK.exists_uniform_generic_fullColour_S1_S2_subcopies
      G J hJLeaf W hRoots Cut
  exact ⟨J, hRange, hAboveOld, hPattern,
    c, p, q, hOneRole, hTwoRole, hAll⟩

end DiaryLeafPriority
end ThreeUniformDiaries
