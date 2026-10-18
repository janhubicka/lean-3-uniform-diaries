import ThreeUniformDiaries.DiaryFiniteDummyTailCrossV3

/-!
# Both Devlin V3 markers between infinite dummy-tail leaves

For dummy vertices n<=u<z the carrier includes marker (1,u,z)
and excludes marker (2,u,z). Their literal LexEarlier comparison
must therefore be TRUE, not merely prescribed by convention.

Every singleton test ending at u and at z below level u agrees:
below n all dummy columns are uniform in the later endpoint,
while between n and u only marker-one tail-tail incidences exist.
Thus oneMeetLevel(u,z) equals its cap u, and the FIRST clause of
the manuscript's literal LexEarlier predicate holds automatically.

This checks both V3 equivalences on ALL pairs of tail leaves,
independent of any finite-to-tail bit choices and using only
finite source edge support.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat} {n : Nat}

/-- At a middle vertex b>=n, the only possible dummy-tail edge
is the marker-one triple (1,b,z), with b<z. -/
theorem finiteDummyTailCarrier_late_column_iff
    (FH : FiniteDiaryEdgeFrame H n)
    (bits : Nat → Bool)
    (a b z : Nat) (hbn : n ≤ b) :
    (finiteDummyTailCarrier H n bits).edge a b z ↔
      (a = 1 ∧ b < z) := by
  constructor
  · intro he
    rcases he with hOld | hCross | hTail
    · have hOrd := FH.edge_support a b z hOld.1
      omega
    · obtain ⟨u,hu3,hun,huLeaf,hzn,hy,hBit⟩ := hCross
      omega
    · exact ⟨hTail.1,hTail.2.2⟩
  · rintro ⟨ha,hbz⟩
    exact Or.inr (Or.inr ⟨ha,hbn,hbz⟩)

/-- Two tail columns agree on ALL singleton tests before the
earlier tail vertex u. -/
theorem finiteDummyTailCarrier_tail_pair_sameOneType
    (FH : FiniteDiaryEdgeFrame H n)
    (bits : Nat → Bool)
    (u z : Nat) (hun : n ≤ u) (huz : u < z) :
    (finiteDummyTailCarrier H n bits).SameOneTypeBelow u u z := by
  intro a b hab hb
  by_cases hbn : b < n
  · exact (finiteDummyTailCarrier_tail_column_iff
        bits a b u hbn hun).trans
      (finiteDummyTailCarrier_tail_column_iff
        bits a b z hbn (by omega)).symm
  · have hbge : n ≤ b := by omega
    have hBU : b < u := hb
    have hBZ : b < z := by omega
    calc
      (finiteDummyTailCarrier H n bits).edge a b u ↔
          (a = 1 ∧ b < u) :=
        finiteDummyTailCarrier_late_column_iff
          FH bits a b u hbge
      _ ↔ (a = 1 ∧ b < z) := by simp only [hBU,hBZ]
      _ ↔ (finiteDummyTailCarrier H n bits).edge a b z :=
        (finiteDummyTailCarrier_late_column_iff
          FH bits a b z hbge).symm

/-- Literal capped singleton meet of ANY two ordered tail
vertices is exactly their earlier vertex u. -/
theorem finiteDummyTailCarrier_tail_pair_oneMeet_capped
    (FH : FiniteDiaryEdgeFrame H n)
    (bits : Nat → Bool)
    (u z : Nat) (hun : n ≤ u) (huz : u < z) :
    (finiteDummyTailCarrier H n bits).oneMeetLevel u z = u := by
  classical
  let G := finiteDummyTailCarrier H n bits
  have hSame : G.SameOneTypeBelow u u z :=
    finiteDummyTailCarrier_tail_pair_sameOneType
      FH bits u z hun huz
  have hCap : G.oneMeetLevel u z ≤ u := by
    have hBound := G.oneMeetLevel_le_min u z
    omega
  have hLower : u ≤ G.oneMeetLevel u z :=
    Nat.le_findGreatest (by omega) hSame
  omega

/-- The actual manuscript LexEarlier is TRUE on every increasing
pair of tail leaves, by its first (capped) disjunct. -/
theorem finiteDummyTailCarrier_tail_pair_LexEarlier
    (FH : FiniteDiaryEdgeFrame H n)
    (bits : Nat → Bool)
    (u z : Nat) (hun : n ≤ u) (huz : u < z) :
    LexEarlier (finiteDummyTailCarrier H n bits) u z := by
  have hMeet := finiteDummyTailCarrier_tail_pair_oneMeet_capped
    FH bits u z hun huz
  exact Or.inl ⟨huz,hMeet⟩

/-- BOTH literal V3 Devlin marker equivalences hold between
arbitrary tail leaves, without restricting or choosing any bits. -/
theorem finiteDummyTailCarrier_tail_pair_V3_both
    (FH : FiniteDiaryEdgeFrame H n)
    (bits : Nat → Bool)
    (u z : Nat) (hun : n ≤ u) (huz : u < z) :
    (((finiteDummyTailCarrier H n bits).edge 1 u z ↔
        LexEarlier (finiteDummyTailCarrier H n bits) u z) ∧
     ((finiteDummyTailCarrier H n bits).edge 2 u z ↔
        ¬ LexEarlier (finiteDummyTailCarrier H n bits) u z)) := by
  have hLex :=
    finiteDummyTailCarrier_tail_pair_LexEarlier FH bits u z hun huz
  have hEdgeOne :=
    finiteDummyTailCarrier_tail_pair_marker_one (H := H)
      bits u z hun huz
  have hNotTwo :=
    finiteDummyTailCarrier_tail_pair_marker_two_false
      FH bits u z hun huz
  exact ⟨⟨fun _ => hLex,fun _ => hEdgeOne⟩,
    iff_of_false hNotTwo (fun h => h hLex)⟩

end DiaryLeafPriority
end ThreeUniformDiaries
