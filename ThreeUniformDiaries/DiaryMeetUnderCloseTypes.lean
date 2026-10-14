import ThreeUniformDiaries.DiaryEmbeddingExactOneMeets
import ThreeUniformDiaries.DiaryPointedMeetCut

/-!
# One-type stabilisation preserves earlier meets with a third vertex

The cut-zero lexicographic orientation argument uses the elementary
tree-of-types fact that two vertices of the same singleton type
through a cut cannot distinguish any earlier first disagreement
with a third vertex.

If a,c agree on their singleton types below M+1, their enumerated
positions and that of b are all above M, and the one-type meet
a∧b occurs by M, then c∧b=a∧b. The proof is entirely finite:
* agreement with b below the meet transfers from a to c;
* the original first-disagreement witness at the meet transfers
  from a to c and prevents the new meet from being later.

The ordered type structure need not arise from a diary; no
auxiliary-pair or type-respecting embedding assumption is involved.
This is useful in the separate three-leaf orientation gadget as
well as in split-placement and meet-preservation checks.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- If two vertices agree on all singleton-type edge bits through
cut M, their meets with a third vertex are equal whenever the
first meet has occurred by M and all three vertex indices are
strictly beyond M. -/
theorem oneMeetLevel_stable_under_close_one_types
    (H : Ordered3Graph Nat) (M a b c : Nat)
    (hma : M < a) (hmb : M < b) (hmc : M < c)
    (hSame : H.SameOneTypeBelow (M+1) a c)
    (hmeet : H.oneMeetLevel a b ≤ M) :
    H.oneMeetLevel c b = H.oneMeetLevel a b := by
  let m := H.oneMeetLevel a b
  have hma' : m < a := by dsimp [m]; omega
  have hmb' : m < b := by dsimp [m]; omega
  have hmc' : m < c := by dsimp [m]; omega
  have hmM : m ≤ M := hmeet
  have hAgree : H.SameOneTypeBelow m c b := by
    intro x y hxy hym
    have hycut : y < M+1 := by omega
    calc
      H.edge x y c ↔ H.edge x y a :=
        (hSame (a := x) (b := y) hxy hycut).symm
      _ ↔ H.edge x y b :=
        H.oneMeetLevel_agree a b hxy hym
  have hLower : m ≤ H.oneMeetLevel c b :=
    (H.oneMeetLevel_ge_iff_sameOneTypeBelow
      m c b (by omega) (by omega)).mpr hAgree
  obtain ⟨z, hz, hDiff⟩ :=
    DiaryLeafPriority.oneMeetLevel_has_first_witness
      H a b m rfl hma' hmb'
  have hzAC : H.edge z m a ↔ H.edge z m c :=
    hSame (a := z) (b := m) hz (by omega)
  have hDiffCB : ¬ (H.edge z m c ↔ H.edge z m b) := by
    intro hCB
    exact hDiff (hzAC.trans hCB)
  have hUpper : H.oneMeetLevel c b ≤ m :=
    H.oneMeetLevel_le_of_edge_disagreement c b z m hz hDiffCB
  exact Nat.le_antisymm hUpper hLower

/-- Equality is symmetric in the close singleton-type vertices.
The location of a previously detected meet is therefore
independent of which representative of the common type is used. -/
theorem oneMeetLevel_stable_under_close_one_types_swap
    (H : Ordered3Graph Nat) (M a b c : Nat)
    (hma : M < a) (hmb : M < b) (hmc : M < c)
    (hSame : H.SameOneTypeBelow (M+1) a c)
    (hmeet : H.oneMeetLevel a b ≤ M) :
    H.oneMeetLevel a b = H.oneMeetLevel c b :=
  (H.oneMeetLevel_stable_under_close_one_types
    M a b c hma hmb hmc hSame hmeet).symm

end Ordered3Graph
end ThreeUniformDiaries
