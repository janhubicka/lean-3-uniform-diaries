import ThreeUniformDiaries.TwoTypeMeetLevel
import ThreeUniformDiaries.DiaryEmbeddingExactOneMeets

/-!
# Early full pair-meet witnesses and 2-split placement

In the diary pre-embedding construction, the image of a source
2-split i is defined as the full 2-type meet of two ordered leaf
pairs. To prove the placement upper bound, one must know that the
first source disagreement at i remains a disagreement after any
ORDERED induced target embedding—even if that map does not preserve
the types at all skipped intermediate target levels.

We prove the contrapositive directly, without a global two-meet
preservation assumption. If target full pair types still agree
through image(i)+1, the target equality of all three components
(two singleton types and their auxiliary pair bit) pulls back along
the induced embedding, forcing the source full pair types to agree
through i+1. This contradicts the source's exact meet at i.

Combined with target type agreement at the predecessor cut, this
places the chosen image of every 2-split in the interval
    image(i-1) < target_pair_meet ≤ image(i).
This is the 2-split analogue of the verified 1-split placement.
No diary role axioms or Ramsey theorem are added.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- An induced increasing target embedding reflects a full
pair-type disagreement at the NEXT source level. In particular,
a target pair-type meet cannot pass beyond the image of the
source's first-disagreement level. -/
theorem twoMeetLevel_le_of_source_type_failure
    {H K : Ordered3Graph Nat}
    (φ : Embedding H K)
    (w a b c d : Nat)
    (hwa : w < a) (hab : a < b)
    (hwc : w < c) (hcd : c < d)
    (hfail : ¬ H.SameTwoTypeBelow (w+1) a b c d) :
    K.twoMeetLevel (φ a) (φ b) (φ c) (φ d) ≤ φ w := by
  by_contra hn
  have hhigh : φ w + 1 ≤
      K.twoMeetLevel (φ a) (φ b) (φ c) (φ d) := by omega
  have htarget : K.SameTwoTypeBelow (φ w+1)
      (φ a) (φ b) (φ c) (φ d) := by
    have h := K.twoMeetLevel_agree (φ a) (φ b) (φ c) (φ d)
    refine ⟨?_, ?_, ?_⟩
    · intro x y hxy hy
      exact h.1 hxy (lt_of_lt_of_le hy hhigh)
    · intro x y hxy hy
      exact h.2.1 hxy (lt_of_lt_of_le hy hhigh)
    · intro x hx
      have hAux : K.SameAuxTypeBelow
          (K.twoMeetLevel (φ a) (φ b) (φ c) (φ d))
          (φ a) (φ b) (φ c) (φ d) := h.2.2
      exact hAux (a := x) (lt_of_lt_of_le hx hhigh)
  have hsource : H.SameTwoTypeBelow (w+1) a b c d := by
    refine ⟨?_, ?_, ?_⟩
    · intro x y hxy hy
      have hyw : y ≤ w := by omega
      have hya : y < a := by omega
      have hyc : y < c := by omega
      have hycut : φ y < φ w + 1 := by
        have he : φ y ≤ φ w := φ.strictMono.monotone hyw
        omega
      calc
        H.edge x y a ↔ K.edge (φ x) (φ y) (φ a) :=
          φ.edge_iff hxy hya
        _ ↔ K.edge (φ x) (φ y) (φ c) :=
          htarget.1 (φ.strictMono hxy) hycut
        _ ↔ H.edge x y c :=
          (φ.edge_iff hxy hyc).symm
    · intro x y hxy hy
      have hyw : y ≤ w := by omega
      have hyb : y < b := by omega
      have hyd : y < d := by omega
      have hycut : φ y < φ w + 1 := by
        have he : φ y ≤ φ w := φ.strictMono.monotone hyw
        omega
      calc
        H.edge x y b ↔ K.edge (φ x) (φ y) (φ b) :=
          φ.edge_iff hxy hyb
        _ ↔ K.edge (φ x) (φ y) (φ d) :=
          htarget.2.1 (φ.strictMono hxy) hycut
        _ ↔ H.edge x y d :=
          (φ.edge_iff hxy hyd).symm
    · intro z hz
      have hzw : z ≤ w := by omega
      have hza : z < a := by omega
      have hzc : z < c := by omega
      have hzcut : φ z < φ w + 1 := by
        have he : φ z ≤ φ w := φ.strictMono.monotone hzw
        omega
      calc
        H.edge z a b ↔ K.edge (φ z) (φ a) (φ b) :=
          φ.edge_iff hza hab
        _ ↔ K.edge (φ z) (φ c) (φ d) := by
          have hAux : K.SameAuxTypeBelow (φ w+1)
              (φ a) (φ b) (φ c) (φ d) := htarget.2.2
          exact hAux (a := φ z) hzcut
        _ ↔ H.edge z c d :=
          (φ.edge_iff hzc hcd).symm
  exact hfail hsource

/-- Placement of the target full 2-type meet corresponding to a
source 2-split i. Predecessor-cut target 2-type agreement gives
the strict lower bound; the source first-disagreement at i and
inducedness give the upper bound. No full two-meet preservation
assumption is required of the target embedding. -/
theorem twoSplit_target_placement
    {H K : Ordered3Graph Nat}
    (φ : Embedding H K)
    (i a b c d : Nat)
    (hi : 0 < i)
    (hia : i < a) (hab : a < b)
    (hic : i < c) (hcd : c < d)
    (hmeet : H.twoMeetLevel a b c d = i)
    (hSame : K.SameTwoTypeBelow
      (φ (i-1)+1) (φ a) (φ b) (φ c) (φ d)) :
    φ (i-1) < K.twoMeetLevel (φ a) (φ b) (φ c) (φ d) ∧
      K.twoMeetLevel (φ a) (φ b) (φ c) (φ d) ≤ φ i := by
  classical
  have hpred : i-1 < i := by omega
  have hpA : φ (i-1) < φ a :=
    φ.strictMono (lt_trans hpred hia)
  have hpC : φ (i-1) < φ c :=
    φ.strictMono (lt_trans hpred hic)
  have hLower : φ (i-1)+1 ≤
      K.twoMeetLevel (φ a) (φ b) (φ c) (φ d) := by
    apply Nat.le_findGreatest (le_min (by omega) (by omega))
    exact hSame
  have hSourceFail : ¬ H.SameTwoTypeBelow (i+1) a b c d := by
    intro hnext
    have hh : i+1 ≤ H.twoMeetLevel a b c d := by
      apply Nat.le_findGreatest (le_min (by omega) (by omega))
      exact hnext
    omega
  have hUpper :
      K.twoMeetLevel (φ a) (φ b) (φ c) (φ d) ≤ φ i :=
    twoMeetLevel_le_of_source_type_failure
      φ i a b c d hia hab hic hcd hSourceFail
  exact ⟨by omega, hUpper⟩

end Ordered3Graph
end ThreeUniformDiaries
