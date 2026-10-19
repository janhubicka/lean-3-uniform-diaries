import ThreeUniformDiaries.DiaryFiniteDummyTailTailV3
import ThreeUniformDiaries.DiaryFiniteDummyTailWitnesses
import ThreeUniformDiaries.DiaryLexPrefixEdgeInvariance

/-!
# Complete countable V/E pre-diary extension of a bounded finite pre-diary

Start with a genuine bounded finite V/E pre-diary, not an artificial
global RolePrediary on an eventually empty ternary edge table.
Append infinitely many marker-defined leaves, with precisely
the cross Devlin bits selected by the already verified finite
causal Boolean fixed point, and with marker-one edges on all
pairs of tail leaves.

This module assembles the REAL global V1/V2/V3/E axioms:
* role validity, positive split coherence and exact split witnesses
  follow from the old source finite pre-diary and preserved meets;
* internal old-old V3 follows from literal LexEarlier invariance
  under the induced old finite edge columns;
* finite-to-tail V3 follows from the causal fixed-point construction;
* tail-to-tail V3 follows from the exact capped meet;
* every edge has one of the five permitted shapes.

The result is a genuine RolePrediary over all Nat. The finite
source remains induced and ALL its old numerical singleton and
full ordered-pair meets are preserved by earlier checked lemmas.
No S1/S2 is claimed for the ambient pre-diary.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat} {n : Nat}

/-- The literal manuscript lexicographic comparison on any
ordered pair of old vertices is unchanged when adding a tail.
No V/E/S source axioms beyond finite edge support are needed. -/
theorem finiteDummyTailCarrier_old_LexEarlier_iff
    (FH : FiniteDiaryEdgeFrame H n)
    (bits : Nat → Bool)
    (a b : Nat) (hab : a < b) (hbn : b < n) :
    (LexEarlier H a b ↔
      LexEarlier (finiteDummyTailCarrier H n bits) a b) := by
  have han : a < n := by omega
  have hA :
      ∀ x y : Nat, x < y → y < a →
        (H.edge x y a ↔
          (finiteDummyTailCarrier H n bits).edge x y a) := by
    intro x y _hxy _hya
    exact (finiteDummyTailCarrier_finite_edge_iff
      FH bits x y a han).symm
  have hB :
      ∀ x y : Nat, x < y → y < a →
        (H.edge x y b ↔
          (finiteDummyTailCarrier H n bits).edge x y b) := by
    intro x y _hxy _hya
    exact (finiteDummyTailCarrier_finite_edge_iff
      FH bits x y b hbn).symm
  exact lexEarlier_prefix_congr_of_edge_columns
    (H := H) (K := finiteDummyTailCarrier H n bits)
    a b hab hA hB

/-- Every edge in the countable dummy-tail carrier satisfies the
actual E1--E5 permitted diary shapes, using target marker roles.
The cross and tail edge shapes are precisely Devlin edges. -/
theorem finiteDummyTailCarrier_permitted_edge
    (P : FiniteRolePrediaryBlock H n)
    (bits : Nat → Bool)
    (x y z : Nat)
    (he : (finiteDummyTailCarrier H n bits).edge x y z) :
    PermittedDiaryEdge (finiteDummyTailCarrier H n bits) x y z := by
  let G := finiteDummyTailCarrier H n bits
  rcases he with hOld | hCross | hTail
  · have hSupp := P.frame.edge_support x y z hOld.1
    have hxn : x < n := by omega
    have hyn : y < n := by omega
    have hzn : z < n := hOld.2
    rcases P.permitted_edge x y z hOld.1 with
        hRole | hOne | hTwo | hDevlin | hNormal
    · exact Or.inl hRole
    · exact Or.inr (Or.inl
        ⟨hOne.1,
         (finiteDummyTailCarrier_old_oneSplit_iff
           P.frame bits y hyn).mpr hOne.2.1,
         (finiteDummyTailCarrier_old_leaf_iff
           P.frame bits z hzn).mpr hOne.2.2⟩)
    · exact Or.inr (Or.inr (Or.inl
        ⟨(finiteDummyTailCarrier_old_twoSplit_iff
           P.frame bits x hxn).mpr hTwo.1,
         (finiteDummyTailCarrier_old_leaf_iff
           P.frame bits y hyn).mpr hTwo.2.1,
         (finiteDummyTailCarrier_old_leaf_iff
           P.frame bits z hzn).mpr hTwo.2.2⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨hDevlin.1,
         (finiteDummyTailCarrier_old_leaf_iff
           P.frame bits y hyn).mpr hDevlin.2.1,
         (finiteDummyTailCarrier_old_leaf_iff
           P.frame bits z hzn).mpr hDevlin.2.2⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨(finiteDummyTailCarrier_old_leaf_iff
           P.frame bits x hxn).mpr hNormal.1,
         (finiteDummyTailCarrier_old_leaf_iff
           P.frame bits y hyn).mpr hNormal.2.1,
         (finiteDummyTailCarrier_old_leaf_iff
           P.frame bits z hzn).mpr hNormal.2.2⟩)))
  · obtain ⟨u,hu3,hun,huLeaf,hzn,hy,hBit⟩ := hCross
    have huG : IsLeaf G u :=
      (finiteDummyTailCarrier_old_leaf_iff
        P.frame bits u hun).mpr huLeaf
    have hzG : IsLeaf G z :=
      finiteDummyTailCarrier_tail_isLeaf P.frame bits z hzn
    have hxMarker : x = 1 ∨ x = 2 :=
      hBit.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
    subst y
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hxMarker,huG,hzG⟩)))
  · obtain ⟨hx,hy,hYZ⟩ := hTail
    have hyG : IsLeaf G y :=
      finiteDummyTailCarrier_tail_isLeaf P.frame bits y hy
    have hzG : IsLeaf G z :=
      finiteDummyTailCarrier_tail_isLeaf P.frame bits z (by omega)
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨Or.inl hx,hyG,hzG⟩)))

/-- One chosen orientation satisfies BOTH literal V3 Devlin
marker equations for ALL pairs of genuine countable target
leaves: old-old, old-to-tail and tail-to-tail. -/
theorem finiteDummyTailCarrier_global_V3
    (P : FiniteRolePrediaryBlock H n)
    (bits : Nat → Bool)
    (hCross : ∀ u z : Nat,
      3 ≤ u → u < n → IsLeaf H u → n ≤ z →
      (((finiteDummyTailCarrier H n bits).edge 1 u z ↔
          LexEarlier (finiteDummyTailCarrier H n bits) u z) ∧
       ((finiteDummyTailCarrier H n bits).edge 2 u z ↔
          ¬ LexEarlier (finiteDummyTailCarrier H n bits) u z))) :
    ∀ a b : Nat, a < b →
      IsLeaf (finiteDummyTailCarrier H n bits) a →
      IsLeaf (finiteDummyTailCarrier H n bits) b →
      (((finiteDummyTailCarrier H n bits).edge 1 a b ↔
          LexEarlier (finiteDummyTailCarrier H n bits) a b) ∧
       ((finiteDummyTailCarrier H n bits).edge 2 a b ↔
          ¬ LexEarlier (finiteDummyTailCarrier H n bits) a b)) := by
  intro a b hab ha hb
  by_cases hbn : b < n
  · have han : a < n := by omega
    have haSource : IsLeaf H a :=
      (finiteDummyTailCarrier_old_leaf_iff
        P.frame bits a han).mp ha
    have hbSource : IsLeaf H b :=
      (finiteDummyTailCarrier_old_leaf_iff
        P.frame bits b hbn).mp hb
    have hLex := finiteDummyTailCarrier_old_LexEarlier_iff
      P.frame bits a b hab hbn
    constructor
    · calc
        (finiteDummyTailCarrier H n bits).edge 1 a b ↔
            H.edge 1 a b :=
          finiteDummyTailCarrier_finite_edge_iff
            P.frame bits 1 a b hbn
        _ ↔ LexEarlier H a b :=
          P.leaf_marker_one a b hab hbn haSource hbSource
        _ ↔ LexEarlier (finiteDummyTailCarrier H n bits) a b :=
          hLex
    · calc
        (finiteDummyTailCarrier H n bits).edge 2 a b ↔
            H.edge 2 a b :=
          finiteDummyTailCarrier_finite_edge_iff
            P.frame bits 2 a b hbn
        _ ↔ ¬ LexEarlier H a b :=
          P.leaf_marker_two a b hab hbn haSource hbSource
        _ ↔ ¬ LexEarlier (finiteDummyTailCarrier H n bits) a b :=
          not_congr hLex
  · have hbg : n ≤ b := by omega
    by_cases han : a < n
    · have haSource : IsLeaf H a :=
        (finiteDummyTailCarrier_old_leaf_iff
          P.frame bits a han).mp ha
      exact hCross a b ha.1 han haSource hbg
    · have hag : n ≤ a := by omega
      exact finiteDummyTailCarrier_tail_pair_V3_both
        P.frame bits a b hag hab

/-- The ACTUAL countable dummy-tail carrier extends every finite
V/E pre-diary block to a full global RolePrediary over Nat.
The witness clauses are genuinely global and both V3 marker
laws are the exact manuscript LexEarlier, not arbitrary bits. -/
theorem exists_finiteDummyTailCarrier_prediary
    (P : FiniteRolePrediaryBlock H n) :
    ∃ bits : Nat → Bool,
      RolePrediary (finiteDummyTailCarrier H n bits) := by
  obtain ⟨bits,hCross⟩ :=
    exists_finiteDummyTailOrientation_cross_V3_both P.frame
  have hV3 := finiteDummyTailCarrier_global_V3 P bits hCross
  refine ⟨bits, {
    role_valid := finiteDummyTailCarrier_role_valid P bits
    one_split_coherent := ?_
    one_split_witness := ?_
    two_split_coherent := ?_
    two_split_witness := ?_
    leaf_marker_one := ?_
    leaf_marker_two := ?_
    edge_ordered := ?_
    permitted_edge := ?_
  }⟩
  · intro s a b hs ha hb hA hB
    exact finiteDummyTailCarrier_oneSplit_coherent
      P bits s a b hs ha hb hA hB
  · intro s hs
    exact finiteDummyTailCarrier_oneSplit_witness
      P bits s hs
  · intro s a b c d hs hab hcd ha hb hc hd hAB hCD
    exact finiteDummyTailCarrier_twoSplit_coherent
      P bits s a b c d hs hab hcd ha hb hc hd hAB hCD
  · intro s hs
    exact finiteDummyTailCarrier_twoSplit_witness
      P bits s hs
  · intro a b hab ha hb
    exact (hV3 a b hab ha hb).1
  · intro a b hab ha hb
    exact (hV3 a b hab ha hb).2
  · intro x y z he
    exact finiteDummyTailCarrier_edge_ordered
      P.frame bits x y z he
  · intro x y z he
    exact finiteDummyTailCarrier_permitted_edge P bits x y z he

end DiaryLeafPriority
end ThreeUniformDiaries
