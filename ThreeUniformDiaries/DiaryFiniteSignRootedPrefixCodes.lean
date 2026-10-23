import ThreeUniformDiaries.DiaryFiniteSignRootedPrefixIncidence
import ThreeUniformDiaries.DiaryFlipPositiveTypeCodes

/-!
# Sign-rooted source prefixes determine the exact finite type codes

The verified source-edge theorem says that two genuine diary flips
with the same global Devlin sign and the same genuine S2 witness
bits strictly below cut m agree on EVERY source incidence (x,y,z)
with x<m.

For original vertices u>=m, this entails literal equality of
their singleton type code, and for ordered source pairs (u,v)
with m<=u<v, literal equality of the COMPLETE ordered pair
type code: both singleton coordinates and all auxiliary tests.
The result remains valid for mixed source roles; the source
coordinate vertices need not be leaves.

This is an explicit, source-side positive-profile compatibility
interface for a future sign-rooted amalgamation of flip branches.
It does NOT construct any cross-branch edges or establish the
V3 and V1/V2 gluing conditions of an ambient pre-diary.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Any two ordered ternary graphs whose strictly increasing
triples agree whenever the first vertex is below m have
identical singleton test codes below m at all source
vertices u>=m. This includes mixed source vertex roles. -/
theorem finite_oneCode_eq_of_edge_prefix
    {P Q : Ordered3Graph Nat} {n m : Nat}
    (hPrefix : ∀ x y z : Nat,
      x < y → y < z → z < n → x < m →
        (P.edge x y z ↔ Q.edge x y z))
    (u : Nat) (hmu : m ≤ u) (hun : u < n) :
    oneCode P m u = oneCode Q m u := by
  classical
  funext x y
  by_cases hxy : x.val < y.val
  · have hTest : P.edge x.val y.val u ↔
        Q.edge x.val y.val u :=
      hPrefix x.val y.val u hxy
        (by omega) hun x.isLt
    simp [oneCode,hxy,hTest]
  · simp [oneCode,hxy]

/-- Exact auxiliary pair-code agreement at cut m follows
from the same edge-prefix hypothesis, for ordered source
vertices m<=u<v<n (not necessarily leaves). -/
theorem finite_auxCode_eq_of_edge_prefix
    {P Q : Ordered3Graph Nat} {n m : Nat}
    (hPrefix : ∀ x y z : Nat,
      x < y → y < z → z < n → x < m →
        (P.edge x y z ↔ Q.edge x y z))
    (u v : Nat) (hmu : m ≤ u)
    (huv : u < v) (hvn : v < n) :
    auxCode P m u v = auxCode Q m u v := by
  classical
  funext x
  have hTest : P.edge x.val u v ↔ Q.edge x.val u v :=
    hPrefix x.val u v (by omega) huv hvn x.isLt
  simp [auxCode,hTest]

/-- Both singleton coordinate codes and the auxiliary pair
code agree when all earlier first-coordinate incidences agree. -/
theorem finite_twoCode_eq_of_edge_prefix
    {P Q : Ordered3Graph Nat} {n m : Nat}
    (hPrefix : ∀ x y z : Nat,
      x < y → y < z → z < n → x < m →
        (P.edge x y z ↔ Q.edge x y z))
    (u v : Nat) (hmu : m ≤ u)
    (huv : u < v) (hvn : v < n) :
    twoCode P m u v = twoCode Q m u v := by
  have hOneU :=
    finite_oneCode_eq_of_edge_prefix hPrefix u hmu (by omega)
  have hOneV :=
    finite_oneCode_eq_of_edge_prefix hPrefix v (by omega) hvn
  have hAux :=
    finite_auxCode_eq_of_edge_prefix hPrefix u v hmu huv hvn
  dsimp only [twoCode]
  exact congrArg₂ (fun x y => (x,y)) hOneU
    (congrArg₂ (fun x y => (x,y)) hOneV hAux)

/-- For two genuine flips of a common finite source A,
agreement of the root marker-one sign and all selected S2
bits before m yields exact equality of the full type CODE
for every ordered source vertex pair above m.

This exports the type-level form of the already verified
sign-rooted prefix edge theorem, with no unproved global
cross-branch type comparisons. -/
theorem finite_signRooted_twoCode_eq_before_cut
    {A P Q : Ordered3Graph Nat} {n : Nat}
    (FP : FiniteDiaryFlip A P n)
    (FQ : FiniteDiaryFlip A Q n)
    (r t m : Nat) (hrt : r < t) (htn : t < n)
    (hr : IsLeaf A r) (ht : IsLeaf A t)
    (hReference : P.edge 1 r t ↔ Q.edge 1 r t)
    (hEarlierS2 :
      ∀ s : Nat, IsTwoSplit A s → s < m →
        ∃ a b c d : Nat,
          a < b ∧ c < d ∧ b < n ∧ d < n ∧
          IsLeaf A a ∧ IsLeaf A b ∧
          IsLeaf A c ∧ IsLeaf A d ∧
          s < a ∧ s < c ∧
          A.twoMeetLevel a b c d = s ∧
          (P.edge s a b ↔ Q.edge s a b))
    (u v : Nat) (hmu : m ≤ u)
    (huv : u < v) (hvn : v < n) :
    twoCode P m u v = twoCode Q m u v := by
  have hPrefix :=
    finite_two_flips_edges_agree_before_cut
      FP FQ r t m hrt htn hr ht hReference hEarlierS2
  exact finite_twoCode_eq_of_edge_prefix hPrefix
    u v hmu huv hvn

end DiaryLeafPriority
end ThreeUniformDiaries
