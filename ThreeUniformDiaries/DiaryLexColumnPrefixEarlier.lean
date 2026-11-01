import ThreeUniformDiaries.DiaryLexColumnPrefixMeets
import ThreeUniformDiaries.DiaryFullRoleDefinition

/-!
# Track B: prefix-identical singleton columns have the same earlier Lex order

The shifted 3-marker seed has a hard V3 compatibility requirement:
adding Devlin edge bits cannot introduce a spurious earlier
singleton disagreement. Its mathematical basis is that, if two
late vertices have identical old singleton columns below m, then
every earlier t <= m has the SAME lexicographic relation to them.

The proof is purely about literal maximal-agreement meets in an
arbitrary ordered 3-graph:
1. the first singleton comparison of t with a or b is equal;
2. if this meet is proper, its deciding full pair-meet is equal;
3. the deciding edge is the same because its middle coordinate
   lies STRICTLY BELOW the common old singleton prefix cut.

The strict cut is essential: the paper's arbitrary ordered edge
predicate need not be irreflexive outside increasing triples,
so it is not legitimate to compare edges with repeated coordinates.
We prove the decisive full meet is proper before using the prefix
agreement to compare its deciding bit.

No diary axioms, Ramsey, or unavoidability are used.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- In a proper singleton comparison r = oneMeet(t,a) < t,a,
the auxiliary pair comparison (r,t),(r,a) must disagree
strictly before r. Otherwise the original singleton types
would agree through the forbidden next cut r+1. -/
theorem auxMeetLevel_lt_proper_firstOneMeet
    (H : Ordered3Graph Nat) (t a : Nat)
    (hta : t < a)
    (hr : H.oneMeetLevel t a < t) :
    H.auxMeetLevel (H.oneMeetLevel t a) t
        (H.oneMeetLevel t a) a <
      H.oneMeetLevel t a := by
  classical
  let r := H.oneMeetLevel t a
  have hauxBound : H.auxMeetLevel r t r a ≤ r := by
    simpa only [min_self] using H.auxMeetLevel_le_min r t r a
  by_contra hn
  have hauxEq : H.auxMeetLevel r t r a = r := by
    change ¬ H.auxMeetLevel r t r a < r at hn
    omega
  have hOldAgree : H.SameOneTypeBelow r t a := by
    change H.SameOneTypeBelow (H.oneMeetLevel t a) t a
    exact H.oneMeetLevel_agree t a
  have hAux : H.SameAuxTypeBelow r r t r a := by
    simpa only [hauxEq] using H.auxMeetLevel_agree r t r a
  have hNext : H.SameOneTypeBelow (r+1) t a := by
    intro x y hxy hyr
    by_cases hBefore : y < r
    · exact hOldAgree hxy hBefore
    · have hyeq : y = r := by omega
      subst y
      exact hAux hxy
  have hBeyond : r + 1 ≤ H.oneMeetLevel t a :=
    Nat.le_findGreatest (by omega) hNext
  change r + 1 ≤ r at hBeyond
  omega

/-- Column-invariance lemma at the exact numerical cuts:
when the singleton columns of a,b agree below m, any earlier
t <= m sees the SAME genuine source LexEarlier relation.

The proof explicitly separates capped and proper singleton meets,
and derives the strict deciding-edge position for the proper case. -/
theorem lexEarlier_eq_of_common_one_prefix
    (H : Ordered3Graph Nat)
    (m t a b : Nat)
    (hAB : H.SameOneTypeBelow m a b)
    (htm : t ≤ m) (hta : t < a) (htb : t < b) :
    DiaryLeafPriority.LexEarlier H t a ↔
      DiaryLeafPriority.LexEarlier H t b := by
  classical
  let r := H.oneMeetLevel t a
  have hOne : H.oneMeetLevel t a = H.oneMeetLevel t b :=
    H.oneMeetLevel_eq_of_common_one_prefix m t a b
      hAB htm hta.le htb.le
  have hMinA : min t a = t := min_eq_left hta.le
  have hMinB : min t b = t := min_eq_left htb.le
  have hFormA :
      DiaryLeafPriority.LexEarlier H t a ↔
        (r = t ∨
          (r < t ∧ H.edge (H.twoMeetLevel r t r a) r a)) := by
    simp [DiaryLeafPriority.LexEarlier, r, hta, hMinA]
  have hFormB :
      DiaryLeafPriority.LexEarlier H t b ↔
        (r = t ∨
          (r < t ∧ H.edge (H.twoMeetLevel r t r b) r b)) := by
    simp [DiaryLeafPriority.LexEarlier, r, htb, hMinB,
      ← hOne]
  rw [hFormA,hFormB]
  by_cases hCap : r = t
  · simp [hCap]
  · have hrlt : r < t := by
      have hBound : r ≤ t := by
        have h := H.oneMeetLevel_le_min t a
        omega
      omega
    have hrm : r < m := by omega
    have hTwo : H.twoMeetLevel r t r a =
        H.twoMeetLevel r t r b :=
      H.twoMeetLevel_eq_of_common_one_prefix
        m r t a b hAB htm hrm hrlt (by omega)
        (by omega) hta.le htb.le
    have hAuxLt :
        H.auxMeetLevel r t r a < r := by
      change H.auxMeetLevel (H.oneMeetLevel t a) t
          (H.oneMeetLevel t a) a < H.oneMeetLevel t a
      exact H.auxMeetLevel_lt_proper_firstOneMeet
        t a hta hrlt
    have hTwoLe : H.twoMeetLevel r t r a ≤
        H.auxMeetLevel r t r a := by
      rw [H.twoMeetLevel_eq_min r t r a hrlt (by omega)]
      exact min_le_left _ _
    have hqLt : H.twoMeetLevel r t r a < r :=
      lt_of_le_of_lt hTwoLe hAuxLt
    have hBit :
        H.edge (H.twoMeetLevel r t r a) r a ↔
          H.edge (H.twoMeetLevel r t r b) r b := by
      rw [← hTwo]
      exact hAB (by omega) (by omega)
    simpa only [hCap, false_or, hrlt, true_and] using hBit

end Ordered3Graph
end ThreeUniformDiaries
