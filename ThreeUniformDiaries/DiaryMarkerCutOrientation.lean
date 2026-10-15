import ThreeUniformDiaries.DiaryFullRoleDefinition
import ThreeUniformDiaries.DiaryMarkerOnePairReduction
import ThreeUniformDiaries.DiaryGappySourceI3TwoSplit
import ThreeUniformDiaries.DiaryOrientationUniformSign

/-!
# At the diary marker cut, full pair types ARE lexicographic orientations

The complete V/E/S diary axioms imply a particularly useful identity.
For increasing ordered pairs of LEAVES, equality of full two-types
below the initial diary cut 3 is exactly equality of their
lexicographic orientations.

Indeed, all leaf singleton types have the same three-marker prefix:
no permitted edge with two vertices below 3 ends in a leaf.
The auxiliary pair type below 3 has just the bits at 0,1,2.
The 0-bit always vanishes, the 1-bit records LexEarlier, and the
2-bit records its complement. Nothing else is visible at that cut.

Therefore the verified genuine gappy-source I3 stabilisation already
forces the target orientation to be CONSTANT on each of the two
source orientation classes.

A second abstract lemma shows that uniformity on these classes
and ONE target-opposite witness with one representative of each
source class imply global relative orientation preservation.
The still-open geometry is thus sharply isolated: produce ONE
opposite-sign target witness whose two source pairs belong to
the opposite diary orientation classes. No new type preservation
across omitted target levels is postulated.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph
open Ordered3Graph.UnorderedEmbedding

namespace RoleDiary

variable {H : Ordered3Graph Nat}

/-- No edge between two vertices of the initial marker
prefix 0,1,2 and a diary leaf is permitted by the five
V/E edge shapes. -/
theorem leaf_no_early_edge (D : RoleDiary H)
    (a x y : Nat) (ha : IsLeaf H a)
    (hxy : x < y) (hy : y < 3) :
    ¬ H.edge x y a := by
  intro he
  rcases D.permitted_edge x y a he with hrole | hone | htwo | hdev | hnormal
  · rcases hrole.2.1 with hy1 | hy2
    · have hx0 : x = 0 := hrole.1
      rw [hx0, hy1] at he
      exact ha.2.1 he
    · have hx0 : x = 0 := hrole.1
      rw [hx0, hy2] at he
      exact ha.2.2 he
  · have hle := (hone.2.1 : IsOneSplit H y).1
    omega
  · have hle := (htwo.1 : IsTwoSplit H x).1
    omega
  · have hle := (hdev.2.1 : IsLeaf H y).1
    omega
  · have hle := (hnormal.1 : IsLeaf H x).1
    omega

/-- All leaves of a complete role-based diary have identical
singleton one-types below marker cut 3. -/
theorem leaf_sameOneTypeBelow_three (D : RoleDiary H)
    (a c : Nat) (ha : IsLeaf H a) (hc : IsLeaf H c) :
    H.SameOneTypeBelow 3 a c := by
  intro x y hxy hy
  exact iff_of_false
    (D.leaf_no_early_edge a x y ha hxy hy)
    (D.leaf_no_early_edge c x y hc hxy hy)

/-- The marker cut 3 sees precisely the LexEarlier orientation
of each increasing ordered leaf pair, not any additional
singleton or auxiliary type information. -/
theorem leaf_sameTwoTypeBelow_three_iff_lex
    (D : RoleDiary H)
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d) :
    H.SameTwoTypeBelow 3 a b c d ↔
      (LexEarlier H a b ↔ LexEarlier H c d) := by
  have hmarkAB : H.edge 1 a b ↔ LexEarlier H a b :=
    D.leaf_marker_one a b hab ha hb
  have hmarkCD : H.edge 1 c d ↔ LexEarlier H c d :=
    D.leaf_marker_one c d hcd hc hd
  have hmark2AB : H.edge 2 a b ↔ ¬ LexEarlier H a b :=
    D.leaf_marker_two a b hab ha hb
  have hmark2CD : H.edge 2 c d ↔ ¬ LexEarlier H c d :=
    D.leaf_marker_two c d hcd hc hd
  constructor
  · intro h
    have hAux : H.SameAuxTypeBelow 3 a b c d := h.2.2
    exact hmarkAB.symm.trans ((hAux (a := 1) (by omega)).trans hmarkCD)
  · intro h
    refine ⟨D.leaf_sameOneTypeBelow_three a c ha hc,
      D.leaf_sameOneTypeBelow_three b d hb hd, ?_⟩
    intro x hx
    have hcases : x = 0 ∨ x = 1 ∨ x = 2 := by omega
    rcases hcases with hzero | hone | htwo
    · subst x
      exact iff_of_false
        (D.zero_leaf_pair_nonedge a b ha)
        (D.zero_leaf_pair_nonedge c d hc)
    · subst x
      exact hmarkAB.trans (h.trans hmarkCD.symm)
    · subst x
      exact hmark2AB.trans ((not_congr h).trans hmark2CD.symm)

/-- Genuine diary-leaf I3 forces equal TARGET lex orientations
for every two ordered source leaf pairs in the same orientation
class. The source embedding may skip levels and the original
outer hypergraph embedding is not assumed increasing. -/
theorem stabilisedSource_lex_same_of_source_lex_same
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    (D : RoleDiary H)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hSame : LexEarlier H a b ↔ LexEarlier H c d) :
    LexEarlier K (stabilisedSource G K F ψ a)
      (stabilisedSource G K F ψ b) ↔
    LexEarlier K (stabilisedSource G K F ψ c)
      (stabilisedSource G K F ψ d) := by
  have hsource : H.SameTwoTypeBelow 3 a b c d :=
    (D.leaf_sameTwoTypeBelow_three_iff_lex
      a b c d hab hcd ha hb hc hd).mpr hSame
  exact (stabilisedSource_diaryLeafPairType_orientation
    G K F D ψ hψ 3 a b c d (by omega)
    (by have ha3 := ha.1; omega)
    (by have hc3 := hc.1; omega)
    hab hcd ha hb hc hd hsource).2

end RoleDiary

/-- Once target orientations are constant on each source
sign class, any two source comparisons with opposite signs
whose target signs are also opposite force global relative
orientation preservation. The two anchors can be arbitrary
points in an arbitrary nonempty comparison system. -/
theorem relative_orientation_of_opposite_anchors
    {ι : Type*} (source target : ι → Prop) (p q : ι)
    (hSourceP : source p) (hSourceQ : ¬ source q)
    (hClass : ∀ x y, (source x ↔ source y) →
      (target x ↔ target y))
    (hTargetOpp : target p ↔ ¬ target q) :
    ∀ x y, (source x ↔ source y) ↔
      (target x ↔ target y) := by
  classical
  have hp (x : ι) : source x → (target x ↔ target p) := by
    intro hx
    exact hClass x p ⟨fun _ => hSourceP, fun _ => hx⟩
  have hq (x : ι) : ¬ source x → (target x ↔ target q) := by
    intro hx
    exact hClass x q ⟨fun hs => False.elim (hx hs),
      fun hs => False.elim (hSourceQ hs)⟩
  intro x y
  have hpx := hp x
  have hpy := hp y
  have hqx := hq x
  have hqy := hq y
  tauto

/-- The complete diary's global relative orientation premise
reduces to ONE opposite-target pair of source leaf-pair
representatives, one positive and one negative. Both same-sign
comparisons are already stable by the genuine diary I3 theorem.
This is the precise remaining geometric witness obligation. -/
theorem stabilisedSource_global_relative_of_opposite_anchor_pairs
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : UnorderedEmbedding G.graph K)
    {H : Ordered3Graph Nat}
    (D : RoleDiary H)
    (ψ : Embedding H G.graph) (hψ : ψ.TypeRespecting)
    (p q : OrderedLeafPair H)
    (hSourceP : LexEarlier H p.first p.second)
    (hSourceQ : ¬ LexEarlier H q.first q.second)
    (hTargetOpp :
      LexEarlier K (stabilisedSource G K F ψ p.first)
        (stabilisedSource G K F ψ p.second) ↔
      ¬ LexEarlier K (stabilisedSource G K F ψ q.first)
        (stabilisedSource G K F ψ q.second)) :
    ∀ r s : OrderedLeafPair H,
      (LexEarlier H r.first r.second ↔
       LexEarlier H s.first s.second) ↔
      (LexEarlier K (stabilisedSource G K F ψ r.first)
         (stabilisedSource G K F ψ r.second) ↔
       LexEarlier K (stabilisedSource G K F ψ s.first)
         (stabilisedSource G K F ψ s.second)) := by
  apply relative_orientation_of_opposite_anchors
    (fun x : OrderedLeafPair H => LexEarlier H x.first x.second)
    (fun x : OrderedLeafPair H =>
      LexEarlier K (stabilisedSource G K F ψ x.first)
        (stabilisedSource G K F ψ x.second))
    p q hSourceP hSourceQ
  · intro r s hSame
    exact D.stabilisedSource_lex_same_of_source_lex_same
      G K F ψ hψ r.first r.second s.first s.second
      r.first_lt_second s.first_lt_second
      r.first_is_leaf r.second_is_leaf
      s.first_is_leaf s.second_is_leaf hSame
  · exact hTargetOpp

end DiaryLeafPriority
end ThreeUniformDiaries
