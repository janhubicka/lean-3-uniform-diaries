import ThreeUniformDiaries.DiaryOnePassV3Reduction
import ThreeUniformDiaries.DiaryOnePassFreshOneMeet

/-!
# Exact lexicographic orientation at a newly selected singleton split

The manuscript's `LexEarlier` uses the full two-type meet of
(m,a) and (m,b), rather than just the first singleton meet m.
Whenever the (0,m,*) edge bits differ, the auxiliary pair meet
is exactly ZERO, so the full pair meet is ZERO too. Hence the
literal LexEarlier comparison is the bit (0,m,b), with no diary
axioms needed.

Apply this to the REAL one-pass singleton event selecting child g
against its realised distinct default h. The concrete selected and
default source leaves have first target singleton meet exactly the
new event (proved previously). The new edge is positive on g and
negative on h. Therefore g is lexicographically AFTER h in the
target in both orientations, independently of their old numerical
positions. This is a verified local orientation component of V3,
not the remaining global source-Lex preservation theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- If (0,m,a) and (0,m,b) differ, then the auxiliary types of
(m,a) and (m,b) already disagree at coordinate zero. -/
theorem auxMeetLevel_zero_of_zero_middle_disagreement
    (G : Ordered3Graph Nat) (m a b : Nat)
    (hDiff : ¬ (G.edge 0 m a ↔ G.edge 0 m b)) :
    G.auxMeetLevel m a m b = 0 := by
  have hAgree := G.auxMeetLevel_agree m a m b
  by_contra hne
  have hpos : 0 < G.auxMeetLevel m a m b := by omega
  exact hDiff (hAgree (a := 0) hpos)

/-- A genuine first singleton split with differing zero-coordinate
edges has LexEarlier oriented by the RIGHT (0,m,b) bit. This does
not require a pre-diary and does not require a<b. -/
theorem lexEarlier_iff_zero_middle_right_of_bit_disagreement
    (G : Ordered3Graph Nat) (m a b : Nat)
    (hma : m < a) (hmb : m < b)
    (hmeet : G.oneMeetLevel a b = m)
    (hDiff : ¬ (G.edge 0 m a ↔ G.edge 0 m b)) :
    LexEarlier G a b ↔ G.edge 0 m b := by
  have hAux : G.auxMeetLevel m a m b = 0 :=
    auxMeetLevel_zero_of_zero_middle_disagreement G m a b hDiff
  have hTwo : G.twoMeetLevel m a m b = 0 := by
    rw [G.twoMeetLevel_eq_min m a m b hma hmb, hAux]
    simp
  change ((a < b ∧ G.oneMeetLevel a b = a) ∨
    (G.oneMeetLevel a b < min a b ∧
      G.edge
        (G.twoMeetLevel (G.oneMeetLevel a b) a
          (G.oneMeetLevel a b) b)
        (G.oneMeetLevel a b) b)) ↔ G.edge 0 m b
  constructor
  · rintro (⟨_, hcap⟩ | ⟨_, he⟩)
    · rw [hmeet] at hcap
      omega
    · simpa only [hmeet, hTwo] using he
  · intro he
    exact Or.inr ⟨by omega, by simpa only [hmeet, hTwo] using he⟩

variable {H : Ordered3Graph Nat}

/-- The selected singleton child is strictly AFTER its default
sibling in the actual target LexEarlier order (in both ordered
directions), witnessed by their genuine fresh event meet. -/
theorem onePass_freshOne_selected_default_lex_orientation
    (P : RolePrediary H) (m : Nat)
    (i : Fin (onePassBlock H m).length)
    (g h : OneGermSpace m)
    (hget : onePassEventAt H m i = BlockEvent.singleton m g)
    (hdef : oneDefaultGerm H m g.1 = some h)
    (hparent : h.1 = g.1)
    (u v : Nat)
    (hu : IsLeaf H u) (hv : IsLeaf H v)
    (hmu : m ≤ u) (hmv : m ≤ v)
    (hug : oneGermCode H m u = g)
    (hvh : oneGermCode H m v = h)
    (hneq : h ≠ g) :
    ¬ LexEarlier (onePassRawTarget H)
        (onePassOldImage H u) (onePassOldImage H v) ∧
      LexEarlier (onePassRawTarget H)
        (onePassOldImage H v) (onePassOldImage H u) := by
  let G := onePassRawTarget H
  let e := onePassEventPosition H m i
  let a := onePassOldImage H u
  let b := onePassOldImage H v
  have hMeet : G.oneMeetLevel a b = e :=
    onePass_freshOne_selected_default_meet_exact P m i
      g h hget hdef hparent u v hu hv hmu hmv hug hvh hneq
  have hPos : G.edge 0 e a :=
    (onePassRawTarget_singleton_incidence_iff H m u i g hget).mpr
      ⟨hu,hmu,hug⟩
  have hNeg : ¬ G.edge 0 e b := by
    intro hb
    have hcode :=
      ((onePassRawTarget_singleton_incidence_iff
        H m v i g hget).mp hb).2.2
    exact hneq (hvh.symm.trans hcode)
  have hDiff : ¬ (G.edge 0 e a ↔ G.edge 0 e b) := by
    intro hEq
    exact hNeg (hEq.mp hPos)
  have hma : e < a :=
    onePassEventPosition_lt_oldImage H m u i hmu
  have hmb : e < b :=
    onePassEventPosition_lt_oldImage H m v i hmv
  have hLexAB : LexEarlier G a b ↔ G.edge 0 e b :=
    lexEarlier_iff_zero_middle_right_of_bit_disagreement
      G e a b hma hmb hMeet hDiff
  have hMeetRev : G.oneMeetLevel b a = e := by
    rw [G.oneMeetLevel_comm]
    exact hMeet
  have hDiffRev : ¬ (G.edge 0 e b ↔ G.edge 0 e a) := by
    intro hEq
    exact hNeg (hEq.mpr hPos)
  have hLexBA : LexEarlier G b a ↔ G.edge 0 e a :=
    lexEarlier_iff_zero_middle_right_of_bit_disagreement
      G e b a hmb hma hMeetRev hDiffRev
  exact ⟨fun h => hNeg (hLexAB.mp h), hLexBA.mpr hPos⟩

end DiaryLeafPriority
end ThreeUniformDiaries
