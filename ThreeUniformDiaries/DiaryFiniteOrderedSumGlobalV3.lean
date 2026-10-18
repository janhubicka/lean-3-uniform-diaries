import ThreeUniformDiaries.DiaryFiniteOrderedSumRoleCases
import ThreeUniformDiaries.DiaryFiniteOrderedSumLeftV3
import ThreeUniformDiaries.DiaryFiniteOrderedSumRightV3
import ThreeUniformDiaries.DiaryFiniteOrderedSumCrossV3

/-!
# Complete finite ordered-sum V3 with an actual causal orientation

The finite raw two-block carrier already has:
* exact left-left Devlin-1 and Devlin-2 marker transport;
* exact right-right Devlin-1 and Devlin-2 marker transport,
  using local S1 and E1--E5 rather than an impossible global
  infinite diary assumption;
* a finite causal Boolean orientation satisfying BOTH cross
  Devlin marker equations simultaneously.

The exhaustive bounded leaf classification now shows these three
cases cover every genuine ordered pair of target leaves in the
combined finite range. Package the existential choice into the
full *finite* V3 statement for all those target leaf pairs.

This is a substantial local theorem, but full finite V/E also
requires witness and positive-class packaging, treated separately.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H K : Ordered3Graph Nat} {n m : Nat}

/-- Every genuine finite target leaf pair satisfies both literal
Devlin V3 clauses after a single globally consistent choice of
cross orientation bits. No global infinite RolePrediary assumed. -/
theorem exists_finiteTwoBlockOrientation_all_V3
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (hEH : ∀ x y z : Nat, H.edge x y z →
      PermittedDiaryEdge H x y z)
    (hEK : ∀ x y z : Nat, K.edge x y z →
      PermittedDiaryEdge K x y z)
    (hH1 : ∀ a b : Nat, a < b → b < n →
      IsLeaf H a → IsLeaf H b →
      (H.edge 1 a b ↔ LexEarlier H a b))
    (hH2 : ∀ a b : Nat, a < b → b < n →
      IsLeaf H a → IsLeaf H b →
      (H.edge 2 a b ↔ ¬ LexEarlier H a b))
    (hKS1 : ∀ a b : Nat, a < b → b < m →
      IsLeaf K a → IsLeaf K b →
      IsOneSplit K (K.oneMeetLevel a b))
    (hK1 : ∀ a b : Nat, a < b → b < m →
      IsLeaf K a → IsLeaf K b →
      (K.edge 1 a b ↔ LexEarlier K a b))
    (hK2 : ∀ a b : Nat, a < b → b < m →
      IsLeaf K a → IsLeaf K b →
      (K.edge 2 a b ↔ ¬ LexEarlier K a b)) :
    ∃ bits : Nat → Bool,
      ∀ a b : Nat, a < b →
        b < finiteTwoBlockLength n m →
        IsLeaf (finiteTwoBlockCarrier H K n m bits) a →
        IsLeaf (finiteTwoBlockCarrier H K n m bits) b →
        (((finiteTwoBlockCarrier H K n m bits).edge 1 a b ↔
            LexEarlier (finiteTwoBlockCarrier H K n m bits) a b) ∧
         ((finiteTwoBlockCarrier H K n m bits).edge 2 a b ↔
            ¬ LexEarlier (finiteTwoBlockCarrier H K n m bits) a b)) := by
  obtain ⟨bits, hCross⟩ :=
    exists_finiteTwoBlockOrientation_cross_V3_both FH FK hEK
  refine ⟨bits, ?_⟩
  intro a b hab hbBound ha hb
  have haBound : a < finiteTwoBlockLength n m := by omega
  rcases finiteTwoBlock_leaf_cases FH FK bits a ha haBound with
      ⟨han,haSource⟩ | ⟨u,hu3,hum,huSource,haEq⟩
  · rcases finiteTwoBlock_leaf_cases FH FK bits b hb hbBound with
        ⟨hbn,hbSource⟩ | ⟨v,hv3,hvm,hvSource,hbEq⟩
    · exact finiteTwoBlockCarrier_left_V3 FH FK bits
        hH1 hH2 a b hab hbn ha hb
    · subst b
      exact hCross a v ha.1 han haSource hv3 hvm hvSource
  · rcases finiteTwoBlock_leaf_cases FH FK bits b hb hbBound with
        ⟨hbn,hbSource⟩ | ⟨v,hv3,hvm,hvSource,hbEq⟩
    · have haRight : n ≤ a := by
        rw [haEq]
        exact rightBlockImage_nonmarker_ge n u
          FH.length_ge_three hu3
      omega
    · subst a
      subst b
      have huv : u < v := by
        by_contra hnot
        have hvu : v ≤ u := by omega
        have hmon := (rightBlockImage_strictMono n
          FH.length_ge_three).monotone hvu
        omega
      exact finiteTwoBlockCarrier_right_V3_both
        FH FK hEH hEK hKS1 hK1 hK2 bits u v
        huv hvm huSource hvSource

end DiaryLeafPriority
end ThreeUniformDiaries
