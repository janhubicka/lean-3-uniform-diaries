import ThreeUniformDiaries.DiaryFiniteStageInducedIntoConditionalEdgeLimit
import ThreeUniformDiaries.DiaryLiteralOldPrefixFullPairMeets

/-!
# Track B: literal finite edge-limit fronts transport all roles and meets

The conditional edge-table colimit of the selected finite strong-absorber
tower was proved in the previously merged Track B modules, assuming the
STILL UNPROVED bounded-forward-ranks property. Here we extend its
eventual complete edge/nonedge prefix equivalence to:
* ALL (not only increasing) raw triples with third coordinate below r;
* all three marker-coded role predicates on every old vertex;
* the numerical singleton and full ordered-pair meets on old vertices.

The exact-meet argument uses only the ALREADY VERIFIED literal-prefix
transport lemmas and does not silently assert that a zero-extended
finite graph is a countable RoleDiary. This module does not yet
transport split witnesses or prove bounded forward ranks.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

namespace FiniteInducedEdgeTower

/-- The eventual prefix theorem also gives literal agreement on
non-increasing triples. Such triples are nonedges on BOTH sides by
the two ordered-edge support theorems. -/
theorem limitGraph_raw_prefix_iff
    (E : FiniteInducedEdgeTower)
    (hp : EventuallyFixedEdgePrefix E.size E.step)
    (r m : Nat) (hm : edgePrefixCutoff hp r ≤ m)
    (a b c : Nat) (hc : c < r) :
    (E.limitGraph hp).edge a b c ↔ E.edge m a b c := by
  by_cases horder : a < b ∧ b < c
  · exact E.limitGraph_edge_iff_late hp r m hm
      a b c horder.1 horder.2 hc
  · have hleft : ¬ (E.limitGraph hp).edge a b c := by
      intro he
      exact horder (E.limitGraph_edge_ordered hp a b c he)
    have hright : ¬ E.edge m a b c := by
      intro he
      exact horder (E.edge_ordered m a b c he)
    exact iff_of_false hleft hright

end FiniteInducedEdgeTower

/-- For the actual SELECTED absorber targets, every sufficiently late
finite stage has exactly the same raw complete edge and nonedge table
as the canonical countable edge limit on an arbitrary fixed prefix.
No finite RoleDiary claim is made about the limit here. -/
theorem selectedAbsorberLimit_literalOldPrefix
    (hb : selectedAbsorberFiniteOrderTower.BoundedRanks)
    (r m : Nat)
    (hm : edgePrefixCutoff
      (selectedAbsorberFiniteEdgeTower_prefix_of_boundedRanks hb) r ≤ m) :
    LiteralOldPrefixAgreement
      (selectedAbsorberFiniteEdgeTower.limitGraph
        (selectedAbsorberFiniteEdgeTower_prefix_of_boundedRanks hb))
      (universalStrongAbsorberTower m).graph r := by
  intro a b c hc
  have h := selectedAbsorberFiniteEdgeTower.limitGraph_raw_prefix_iff
      (selectedAbsorberFiniteEdgeTower_prefix_of_boundedRanks hb)
      r m hm a b c hc
  simpa only [selectedAbsorberFiniteEdgeTower] using h

/-- A SINGLE eventual finite cutoff suffices to transfer ALL
marker roles and exact capped one- and two-type meets on the
fixed literal prefix. This is stronger than checking independent
edge tests at independently chosen horizons. -/
theorem selectedAbsorberLimit_exactPrefixStructure
    (hb : selectedAbsorberFiniteOrderTower.BoundedRanks)
    (r m : Nat)
    (hm : edgePrefixCutoff
      (selectedAbsorberFiniteEdgeTower_prefix_of_boundedRanks hb) r ≤ m) :
    let K := selectedAbsorberFiniteEdgeTower.limitGraph
      (selectedAbsorberFiniteEdgeTower_prefix_of_boundedRanks hb)
    let B := (universalStrongAbsorberTower m).graph
    (∀ u : Nat, u < r →
      (IsLeaf K u ↔ IsLeaf B u) ∧
      (IsOneSplit K u ↔ IsOneSplit B u) ∧
      (IsTwoSplit K u ↔ IsTwoSplit B u)) ∧
    (∀ u v : Nat, u < r → v < r →
      K.oneMeetLevel u v = B.oneMeetLevel u v) ∧
    (∀ a b c d : Nat, a < r → b < r → c < r → d < r →
      K.twoMeetLevel a b c d = B.twoMeetLevel a b c d) := by
  dsimp only
  have h := selectedAbsorberLimit_literalOldPrefix hb r m hm
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    exact role_iff_of_literalOldPrefix h u hu
  · intro u v hu hv
    exact oneMeetLevel_eq_of_literalOldPrefix h u v hu hv
  · intro a b c d ha hb hc hd
    exact twoMeetLevel_eq_of_literalOldPrefix
      h a b c d ha hb hc hd

/-- Uniformity in the horizon: the same exact marker-role,
singleton-meet and full-pair-meet preservation holds in ALL
sufficiently late genuine finite absorber stages. -/
theorem selectedAbsorberLimit_eventual_exactPrefixStructure
    (hb : selectedAbsorberFiniteOrderTower.BoundedRanks)
    (r : Nat) :
    ∃ N : Nat, ∀ m : Nat, N ≤ m →
      let K := selectedAbsorberFiniteEdgeTower.limitGraph
        (selectedAbsorberFiniteEdgeTower_prefix_of_boundedRanks hb)
      let B := (universalStrongAbsorberTower m).graph
      (∀ u : Nat, u < r →
        (IsLeaf K u ↔ IsLeaf B u) ∧
        (IsOneSplit K u ↔ IsOneSplit B u) ∧
        (IsTwoSplit K u ↔ IsTwoSplit B u)) ∧
      (∀ u v : Nat, u < r → v < r →
        K.oneMeetLevel u v = B.oneMeetLevel u v) ∧
      (∀ a b c d : Nat, a < r → b < r → c < r → d < r →
        K.twoMeetLevel a b c d = B.twoMeetLevel a b c d) := by
  refine ⟨edgePrefixCutoff
    (selectedAbsorberFiniteEdgeTower_prefix_of_boundedRanks hb) r, ?_⟩
  intro m hm
  exact selectedAbsorberLimit_exactPrefixStructure hb r m hm

end DiaryLeafPriority
end ThreeUniformDiaries
