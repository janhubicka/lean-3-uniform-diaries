import ThreeUniformDiaries.DiaryOnePassFreshLexOrientation
import ThreeUniformDiaries.TwoTypeMeetLevel

/-!
# Source lex comparison reduces exactly to the mixed auxiliary meet

The manuscript defines LexEarlier through a FULL two-type meet of
the pairs (m,a),(m,b), where m is the singleton meet of a,b.
There is no need to guess an orientation using a zero marker:
for any non-capped singleton meet m<min(a,b), the FULL mixed
pair meet is exactly its auxiliary component. The two singleton
components are both capped at m.

This independent algebraic reduction holds for any ordered 3-graph,
without source S1/S2 and without assumptions about the output of
one-pass completion. It isolates the precise FIRST DIFFERING
source coordinate q needed to prove V3 from binary child ranks.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

/-- A singleton-type is identical to itself at every cut up to
its own vertex, so the capped singleton meet is that vertex. -/
theorem onePass_oneMeetLevel_self
    (G : Ordered3Graph Nat) (m : Nat) :
    G.oneMeetLevel m m = m := by
  apply Nat.le_antisymm
  · simpa using G.oneMeetLevel_le_min m m
  · apply Nat.le_findGreatest (by simp)
    intro x y hxy hy
    rfl

/-- If m is the proper first singleton meet of a,b, the full
two-type meet of the pairs (m,a),(m,b) is EXACTLY their auxiliary
pair meet. No split or marker axioms are required. -/
theorem onePass_twoMeet_mixed_eq_aux
    (G : Ordered3Graph Nat) (m a b : Nat)
    (hma : m < a) (hmb : m < b)
    (hmeet : G.oneMeetLevel a b = m) :
    G.twoMeetLevel m a m b = G.auxMeetLevel m a m b := by
  have hSelf : G.oneMeetLevel m m = m :=
    onePass_oneMeetLevel_self G m
  have hBound : G.auxMeetLevel m a m b ≤ m := by
    simpa using (G.auxMeetLevel_le_min m a m b)
  rw [G.twoMeetLevel_eq_min m a m b hma hmb, hSelf, hmeet]
  simp [min_eq_left hBound]

/-- Literal manuscript LexEarlier for a proper source singleton
meet m is simply the RIGHT incidence bit read at the mixed
auxiliary meet q. This is the first step towards relating it
to finite next-cut singleton-code binary ranks. -/
theorem onePass_lexEarlier_iff_mixedAux_right
    (G : Ordered3Graph Nat) (m a b : Nat)
    (hma : m < a) (hmb : m < b)
    (hmeet : G.oneMeetLevel a b = m) :
    LexEarlier G a b ↔
      G.edge (G.auxMeetLevel m a m b) m b := by
  have hMixed : G.twoMeetLevel m a m b =
      G.auxMeetLevel m a m b :=
    onePass_twoMeet_mixed_eq_aux G m a b hma hmb hmeet
  change ((a < b ∧ G.oneMeetLevel a b = a) ∨
    (G.oneMeetLevel a b < min a b ∧
      G.edge
        (G.twoMeetLevel (G.oneMeetLevel a b) a
          (G.oneMeetLevel a b) b)
        (G.oneMeetLevel a b) b)) ↔
      G.edge (G.auxMeetLevel m a m b) m b
  constructor
  · rintro (⟨_,hcap⟩ | ⟨_,he⟩)
    · rw [hmeet] at hcap
      omega
    · simpa only [hmeet,hMixed] using he
  · intro he
    exact Or.inr
      ⟨by omega, by simpa only [hmeet,hMixed] using he⟩

end DiaryLeafPriority
end ThreeUniformDiaries
