import ThreeUniformDiaries.DiaryFullRoleDefinition

/-!
# Marker-one pair meets are exactly opposite lexicographic orientations

For two ordered pairs of diary leaves, the full 2-type meet is 1
exactly when their lexicographic orientation bits are opposite.

The proof uses only the concrete role-based V/E/S diary axioms:
* a zero marker cannot be joined to two leaves by an edge;
* the marker-one incidence is equivalent to LexEarlier;
* S1 ensures both coordinate singleton meets are later than 1;
* S2 says a full leaf-pair meet is capped, 1, or a 2-split;
* the already validated leaf-priority lemma identifies the
  full pair meet with its auxiliary meet.

This is the precise remaining marker-1 case in the pre-embedding.
It reduces the target-meet assertion to the RELATIVE orientation
comparison of the two ordered leaf pairs: a simultaneous global
flip of all comparisons is harmless. The cut-zero gadget's global
orientation propagation is still a separate task.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RoleDiary

variable {H : Ordered3Graph Nat} (D : RoleDiary H)

/-- The permitted diary edge shapes exclude a triple of the form
(0,a,b) when a and b are leaves. The only allowed edges with
first marker zero have middle position marker 1/2 or a 1-split. -/
theorem zero_leaf_pair_nonedge (D : RoleDiary H)
    (a b : Nat) (ha : IsLeaf H a) :
    ¬ H.edge 0 a b := by
  intro he
  rcases D.permitted_edge 0 a b he with hrole | hone | htwo | hdevlin | hnormal
  · rcases hrole.2.1 with h | h <;> omega
  · exact ha.2.1 hone.2.1.2.1
  · have hbound := htwo.1.1
    omega
  · rcases hdevlin.1 with h | h <;> omega
  · have hbound := hnormal.1.1
    omega

/-- Opposite lexicographic orientation is equivalent to full
leaf-pair type meet at marker 1. This uses only the actual
full 2-type meet and the role-based edge conditions. -/
theorem leaf_pair_twoMeet_eq_one_iff_oppositeLex (D : RoleDiary H)
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d) :
    H.twoMeetLevel a b c d = 1 ↔
      (LexEarlier H a b ↔ ¬ LexEarlier H c d) := by
  classical
  have hMarkAB : H.edge 1 a b ↔ LexEarlier H a b :=
    D.leaf_marker_one a b hab ha hb
  have hMarkCD : H.edge 1 c d ↔ LexEarlier H c d :=
    D.leaf_marker_one c d hcd hc hd
  constructor
  · intro hmeet
    have hauxeq : H.auxMeetLevel a b c d =
        H.twoMeetLevel a b c d :=
      D.roleMeets.leaf_aux_eq_full hab hcd ha hb hc hd
    have haux : H.auxMeetLevel a b c d = 1 := by
      omega
    have hfail : ¬ H.SameAuxTypeBelow 2 a b c d := by
      intro hsame
      have hcap : 2 ≤ min a c := by
        have ha3 := ha.1
        have hc3 := hc.1
        omega
      have hmore : 2 ≤ H.auxMeetLevel a b c d :=
        Nat.le_findGreatest hcap hsame
      omega
    have hmarkDiff : ¬ (H.edge 1 a b ↔ H.edge 1 c d) := by
      intro hbits
      apply hfail
      intro x hx
      have hcases : x = 0 ∨ x = 1 := by omega
      rcases hcases with hzero | hone
      · subst x
        exact iff_of_false
          (D.zero_leaf_pair_nonedge a b ha)
          (D.zero_leaf_pair_nonedge c d hc)
      · subst x
        exact hbits
    tauto
  · intro hOpposite
    have hmarkDiff : ¬ (H.edge 1 a b ↔ H.edge 1 c d) := by
      tauto
    have hupper : H.twoMeetLevel a b c d ≤ 1 := by
      by_contra hn
      have hge : 1 < H.twoMeetLevel a b c d := by omega
      have heq : H.edge 1 a b ↔ H.edge 1 c d :=
        (H.twoMeetLevel_agree a b c d).2.2 (a := 1) hge
      exact hmarkDiff heq
    rcases D.pair_meets a b c d hab hcd ha hb hc hd with
      hcap | hone | htwo
    · have hmin : 1 < min a c := by
        have ha3 := ha.1
        have hc3 := hc.1
        omega
      omega
    · exact hone
    · have htwo3 := htwo.1
      omega

/-- Exact orientation synchronisation needed at the marker-1
step: preserving the equality/difference pattern of two
lexicographic comparisons (rather than their individual signs)
is enough to preserve their marker-1 full pair meet. -/
theorem markerOne_pairMeet_transfer_of_relative_orientation (D : RoleDiary H)
    {K : Ordered3Graph Nat} (E : RoleDiary K)
    (φ : Ordered3Graph.Embedding H K)
    (a b c d : Nat)
    (hab : a < b) (hcd : c < d)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (haT : IsLeaf K (φ a)) (hbT : IsLeaf K (φ b))
    (hcT : IsLeaf K (φ c)) (hdT : IsLeaf K (φ d))
    (hsource : H.twoMeetLevel a b c d = 1)
    (hrelative :
      (LexEarlier H a b ↔ LexEarlier H c d) ↔
        (LexEarlier K (φ a) (φ b) ↔
         LexEarlier K (φ c) (φ d))) :
    K.twoMeetLevel (φ a) (φ b) (φ c) (φ d) = 1 := by
  have hsourceOpp :=
    (D.leaf_pair_twoMeet_eq_one_iff_oppositeLex
      a b c d hab hcd ha hb hc hd).mp hsource
  have htargetOpp :
      LexEarlier K (φ a) (φ b) ↔
        ¬ LexEarlier K (φ c) (φ d) := by
    tauto
  exact (E.leaf_pair_twoMeet_eq_one_iff_oppositeLex
    (φ a) (φ b) (φ c) (φ d)
    (φ.strictMono hab) (φ.strictMono hcd)
    haT hbT hcT hdT).mpr htargetOpp

end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
