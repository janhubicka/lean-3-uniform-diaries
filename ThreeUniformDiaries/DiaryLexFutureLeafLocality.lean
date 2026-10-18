import ThreeUniformDiaries.DiarySourceLexFirstAuxBit

/-!
# Locality of the diary lexicographic comparison

The manuscript's LexEarlier(x,y) for x<y depends ONLY on the
singleton type of y through the cut x. In particular, it does
not read its own yet-unassigned Devlin marker (1,x,y) or (2,x,y).

This is the crucial noncircularity lemma for choosing cross-copy
Devlin markers by increasing earlier leaf in an ordered-sum
amalgamation: two future leaves having identical type through x
must have the same lexicographic orientation relative to x.

All lemmas here hold in an arbitrary ordered ternary edge graph.
No pre-diary or full diary axioms are used.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H : Ordered3Graph Nat}

/-- Equality of a later vertex's singleton type below x makes
every comparison with x identical at all smaller cuts. -/
theorem oneType_right_congr
    (H : Ordered3Graph Nat) (x y z l : Nat)
    (hl : l ≤ x) (h : H.SameOneTypeBelow x y z) :
    (H.SameOneTypeBelow l x y ↔ H.SameOneTypeBelow l x z) := by
  constructor
  · intro hxy a b hab hb
    exact (hxy hab hb).trans (h hab (by omega))
  · intro hxz a b hab hb
    exact (hxz hab hb).trans (h hab (by omega)).symm

/-- The singleton meet of x with a later vertex depends only
on that vertex's singleton code below x. -/
theorem oneMeet_right_congr
    (H : Ordered3Graph Nat) (x y z : Nat)
    (hxy : x < y) (hxz : x < z)
    (h : H.SameOneTypeBelow x y z) :
    H.oneMeetLevel x y = H.oneMeetLevel x z := by
  classical
  have hboundY : H.oneMeetLevel x y ≤ x := by
    have hle := H.oneMeetLevel_le_min x y
    omega
  have hboundZ : H.oneMeetLevel x z ≤ x := by
    have hle := H.oneMeetLevel_le_min x z
    omega
  apply le_antisymm
  · apply Nat.le_findGreatest (by omega)
    exact (oneType_right_congr H x y z (H.oneMeetLevel x y)
      hboundY h).mp (H.oneMeetLevel_agree x y)
  · apply Nat.le_findGreatest (by omega)
    exact (oneType_right_congr H x y z (H.oneMeetLevel x z)
      hboundZ h).mpr (H.oneMeetLevel_agree x z)

/-- The auxiliary meet of (m,x) with (m,y) only reads
the singleton tests of y in column m. Changing y to z
without changing its type through x preserves that meet. -/
theorem mixedAux_right_congr
    (H : Ordered3Graph Nat) (m x y z : Nat)
    (hmx : m < x)
    (h : H.SameOneTypeBelow x y z) :
    H.auxMeetLevel m x m y = H.auxMeetLevel m x m z := by
  classical
  have hcuts (l : Nat) (hl : l ≤ m) :
      (H.SameAuxTypeBelow l m x m y ↔
       H.SameAuxTypeBelow l m x m z) := by
    constructor
    · intro ha t ht
      exact (ha ht).trans (h (by omega : t < m) hmx)
    · intro ha t ht
      exact (ha ht).trans (h (by omega : t < m) hmx).symm
  have hboundY : H.auxMeetLevel m x m y ≤ m := by
    simpa using H.auxMeetLevel_le_min m x m y
  have hboundZ : H.auxMeetLevel m x m z ≤ m := by
    simpa using H.auxMeetLevel_le_min m x m z
  apply le_antisymm
  · apply Nat.le_findGreatest (by omega)
    exact (hcuts (H.auxMeetLevel m x m y) hboundY).mp
      (H.auxMeetLevel_agree m x m y)
  · apply Nat.le_findGreatest (by omega)
    exact (hcuts (H.auxMeetLevel m x m z) hboundZ).mpr
      (H.auxMeetLevel_agree m x m z)

/-- CORE LEX LOCALITY: for x<y,z, identical singleton types
below x imply the same lexicographic comparison of x with y
and of x with z. The proof handles the capped and proper
one-meet cases separately, using the actual first differing
mixed auxiliary coordinate in the proper case. -/
theorem lexEarlier_right_congr_of_sameOneTypeBelow
    (H : Ordered3Graph Nat) (x y z : Nat)
    (hxy : x < y) (hxz : x < z)
    (h : H.SameOneTypeBelow x y z) :
    LexEarlier H x y ↔ LexEarlier H x z := by
  let m := H.oneMeetLevel x y
  have hmeet : H.oneMeetLevel x z = m := by
    simpa only [m] using
      (oneMeet_right_congr H x y z hxy hxz h).symm
  have hmle : m ≤ x := by
    have hb := H.oneMeetLevel_le_min x y
    dsimp [m]
    omega
  by_cases hcap : m = x
  · have hLeft : LexEarlier H x y := by
      exact Or.inl ⟨hxy, by simpa only [m] using hcap⟩
    have hRight : LexEarlier H x z := by
      exact Or.inl ⟨hxz, by rw [hmeet]; exact hcap⟩
    exact ⟨fun _ => hRight, fun _ => hLeft⟩
  · have hmx : m < x := by omega
    have hmy : m < y := by omega
    have hmz : m < z := by omega
    have hAux : H.auxMeetLevel m x m y =
        H.auxMeetLevel m x m z :=
      mixedAux_right_congr H m x y z hmx h
    have hAuxLt : H.auxMeetLevel m x m z < m := by
      have hFrom :=
        (onePass_source_mixedAux_first_difference
          H m x z hmx hmz hmeet).1
      exact hFrom
    have hY :
        LexEarlier H x y ↔
          H.edge (H.auxMeetLevel m x m y) m y :=
      onePass_lexEarlier_iff_mixedAux_right H m x y
        hmx hmy rfl
    have hZ :
        LexEarlier H x z ↔
          H.edge (H.auxMeetLevel m x m z) m z :=
      onePass_lexEarlier_iff_mixedAux_right H m x z
        hmx hmz hmeet
    calc
      LexEarlier H x y ↔
          H.edge (H.auxMeetLevel m x m y) m y := hY
      _ ↔ H.edge (H.auxMeetLevel m x m z) m z := by
        rw [hAux]
        exact h hAuxLt hmx
      _ ↔ LexEarlier H x z := hZ.symm

end DiaryLeafPriority
end ThreeUniformDiaries
