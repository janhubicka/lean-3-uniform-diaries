import ThreeUniformDiaries.DiaryOuterGenericLeafPatternRealization
import ThreeUniformDiaries.DiaryCountableRelativeStepExtension

/-!
# Track C: future genericity over a protected old pair needs multiple colours

English proof and adversarial audit:
  janhubicka/3-uniform-diaries PR #286

A complete mixed singleton mask at target cut B contains the incidence
bit to EVERY ordered pair of earlier vertices u<v<B. Consequently,
placing two future leaves in one B-colour class forces their edge
values over each such old pair to agree. This holds even when the old
pair itself stays OUTSIDE the future reservoir.

Conversely, in an actual generic leaf subcopy, both values over any
fixed old pair from that subcopy occur arbitrarily late, so they
necessarily occupy DIFFERENT finite singleton-colour classes.

These theorems rule out a naive single-colour future tail, not a
multicolour relative construction or countable diary unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Every target old-pair incidence is already a coordinate of the
complete singleton colour at a cut above that pair. The old pair
need NOT itself belong to the future colour class. Full RoleDiary
axioms and target leaf roles are unnecessary. -/
theorem same_singletonColour_forces_same_old_pair_edge
    (K : Ordered3Graph Nat)
    (B u v w w' : Nat)
    (huv : u < v) (hvB : v < B)
    (hColour :
      DiaryLowerBoundColors.singletonColour K B w =
        DiaryLowerBoundColors.singletonColour K B w') :
    (K.edge u v w ↔ K.edge u v w') := by
  have hType : K.SameOneTypeBelow B w w' :=
    (DiaryLowerBoundColors.singletonColour_eq_iff K B w w').mp
      hColour
  exact hType huv hvB

/-- In an ACTUAL admissible stage with complete generated support,
if two future source vertices land in the same mixed colour class at
a cut above a selected old pair, their source edge bits over the
old pair agree. Numerical order and all nonedge tests are respected. -/
theorem AdmissibleCofinalDiaryStage.source_old_pair_edge_iff_of_future_colour_eq
    {H K : Ordered3Graph Nat} {F g : Nat → Nat} {m B a b x y : Nat}
    (Q : AdmissibleCofinalDiaryStage H K F m g)
    (ha : a ∈ countableDiaryFiniteSupport H m)
    (hb : b ∈ countableDiaryFiniteSupport H m)
    (hx : x ∈ countableDiaryFiniteSupport H m)
    (hy : y ∈ countableDiaryFiniteSupport H m)
    (hab : a < b) (hbx : b < x) (hby : b < y)
    (hbB : g b < B)
    (hColour :
      DiaryLowerBoundColors.singletonColour K B (g x) =
        DiaryLowerBoundColors.singletonColour K B (g y)) :
    (H.edge a b x ↔ H.edge a b y) := by
  have hOldOrder : g a < g b :=
    Q.ordered a b ha hb hab
  have hSameTarget :
      (K.edge (g a) (g b) (g x) ↔
        K.edge (g a) (g b) (g y)) :=
    same_singletonColour_forces_same_old_pair_edge
      K B (g a) (g b) (g x) (g y)
      hOldOrder hbB hColour
  exact (Q.induced_edge a b x ha hb hx hab hbx).trans
    (hSameTarget.trans
      (Q.induced_edge a b y ha hb hy hab hby).symm)

/-- Two genuine supported future source vertices requiring opposite
edge signs over a protected old pair CANNOT be put into the same
finite complete singleton-colour cone above the old pair, even if
the old pair is kept outside that cone. -/
theorem AdmissibleCofinalDiaryStage.opposite_old_pair_edges_force_different_colours
    {H K : Ordered3Graph Nat} {F g : Nat → Nat} {m B a b x y : Nat}
    (Q : AdmissibleCofinalDiaryStage H K F m g)
    (ha : a ∈ countableDiaryFiniteSupport H m)
    (hb : b ∈ countableDiaryFiniteSupport H m)
    (hx : x ∈ countableDiaryFiniteSupport H m)
    (hy : y ∈ countableDiaryFiniteSupport H m)
    (hab : a < b) (hbx : b < x) (hby : b < y)
    (hbB : g b < B)
    (hOpp : ¬ (H.edge a b x ↔ H.edge a b y)) :
    DiaryLowerBoundColors.singletonColour K B (g x) ≠
      DiaryLowerBoundColors.singletonColour K B (g y) := by
  intro hColour
  exact hOpp
    (Q.source_old_pair_edge_iff_of_future_colour_eq
      ha hb hx hy hab hbx hby hbB hColour)

/-- In the SAME original unordered induced image of an enumerated
generic 3-hypergraph, an old target-ordered pair F i < F j < B has
arbitrarily late true leaf witnesses for BOTH positive and negative
incidences. Their mixed singleton colours at cut B are different.

This is only the leaf-leaf-future-leaf part of a relative geometric
extension: no split roles, S1/S2 numerical meets or persistent
next-leaf images are supplied. -/
theorem exists_opposite_generic_leaf_tail_singletonColours
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : _root_.ThreeUniformDiaries.Ordered3Graph.UnorderedEmbedding G.graph K)
    (hLeaves : ∀ n : Nat, IsLeaf K (F n))
    (i j B M : Nat) (hij : F i < F j) (hjB : F j < B) :
    ∃ p q : Nat,
      max B M < F p ∧ max B M < F q ∧
      IsLeaf K (F p) ∧ IsLeaf K (F q) ∧
      K.edge (F i) (F j) (F p) ∧
      ¬ K.edge (F i) (F j) (F q) ∧
      DiaryLowerBoundColors.singletonColour K B (F p) ≠
        DiaryLowerBoundColors.singletonColour K B (F q) := by
  obtain ⟨p, hp, hPos⟩ :=
    exists_outer_generic_vertex_positive_on_bounded_pairs
      G K F B (max B M)
  obtain ⟨q, hq, hNeg⟩ :=
    exists_outer_generic_vertex_negative_on_bounded_pairs
      G K F B (max B M)
  have hP := hPos i j hij hjB
  have hN := hNeg i j hij hjB
  refine ⟨p, q, hp, hq, hLeaves p, hLeaves q, hP, hN, ?_⟩
  intro hColour
  have hSame :
      (K.edge (F i) (F j) (F p) ↔
        K.edge (F i) (F j) (F q)) :=
    same_singletonColour_forces_same_old_pair_edge
      K B (F i) (F j) (F p) (F q)
      hij hjB hColour
  exact hN (hSame.mp hP)

end DiaryLeafPriority
end ThreeUniformDiaries
