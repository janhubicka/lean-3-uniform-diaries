import ThreeUniformDiaries.TwoTypeMeetLevel
import ThreeUniformDiaries.ExactTypeMeetLevels

/-!
# Local finite first-disagreement certificates for diary type meets

The ordinary one- and two-type meet levels are defined using
Nat.findGreatest over an interval of possible cuts. For explicit
small diaries it is preferable to certify their exact values
from two short facts:

* agreement at the proposed meet cut;
* an actual edge incidence which disagrees at that cut.

For singleton meets the witness is (x,m,u)/(x,m,v), x<m.
For full ordered-pair meets a differing E3 auxiliary edge
(m,a,b)/(m,c,d) is a sufficient witness.

These are unconditional consequences of the literal meet
definitions. They do not presume the graph is a diary, and
allow concrete source/target computations without unfolding
the noncomputable findGreatest expression.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A bounded one-type agreement together with a literal new
singleton edge disagreement fixes the last-agreement cut. -/
theorem Ordered3Graph.oneMeetLevel_eq_of_first_disagreement
    (H : Ordered3Graph Nat)
    (u v m : Nat)
    (hm : m < min u v)
    (hAgree : H.SameOneTypeBelow m u v)
    (hWitness : ∃ x : Nat, x < m ∧
      ¬ (H.edge x m u ↔ H.edge x m v)) :
    H.oneMeetLevel u v = m := by
  classical
  have hLower : m ≤ H.oneMeetLevel u v :=
    Nat.le_findGreatest hm.le hAgree
  have hNotNext : ¬ H.SameOneTypeBelow (m + 1) u v := by
    intro hNext
    obtain ⟨x,hxm,hdiff⟩ := hWitness
    exact hdiff (hNext hxm (by omega))
  have hUpper : H.oneMeetLevel u v ≤ m := by
    by_contra h
    have hBig : m + 1 ≤ H.oneMeetLevel u v := by omega
    have hFull := H.oneMeetLevel_agree u v
    apply hNotNext
    intro a b hab hb
    exact hFull hab (by omega)
  omega

/-- An actual E3 auxiliary edge disagreement at a cut where
the full ordered pair types still agree establishes their exact
full meet level. Both first coordinates must be later than m;
the pairs themselves are strictly increasing. -/
theorem Ordered3Graph.twoMeetLevel_eq_of_aux_first_disagreement
    (H : Ordered3Graph Nat)
    (a b c d m : Nat)
    (hm : m < min a c)
    (hAgree : H.SameTwoTypeBelow m a b c d)
    (hDifferent : ¬ (H.edge m a b ↔ H.edge m c d)) :
    H.twoMeetLevel a b c d = m := by
  classical
  have hLower : m ≤ H.twoMeetLevel a b c d :=
    Nat.le_findGreatest hm.le hAgree
  have hNotNext : ¬ H.SameTwoTypeBelow (m + 1) a b c d := by
    intro hNext
    exact hDifferent (hNext.2.2 (by omega))
  have hUpper : H.twoMeetLevel a b c d ≤ m := by
    by_contra h
    have hBig : m + 1 ≤ H.twoMeetLevel a b c d := by omega
    have hFull := H.twoMeetLevel_agree a b c d
    apply hNotNext
    refine ⟨?_, ?_, ?_⟩
    · intro x y hxy hy
      exact hFull.1 hxy (by omega)
    · intro x y hxy hy
      exact hFull.2.1 hxy (by omega)
    · intro x hx
      exact hFull.2.2 (by omega)
  omega

end DiaryLeafPriority
end ThreeUniformDiaries
