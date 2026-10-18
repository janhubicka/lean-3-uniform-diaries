import ThreeUniformDiaries.DiaryLexFutureLeafLocality

/-!
# LexEarlier invariance under changes to later edge columns

If two ordered ternary graphs have identical singleton test
columns ending at x and y strictly below the cut x, then their
literal LexEarlier(x,y) comparisons agree whenever x<y.

This is the precise dependency lemma needed for a well-founded
choice of cross-copy Devlin bits: changing an orientation bit
at x (or at any later left vertex) cannot change the comparison
used to choose that bit. No V/E/S diary axiom is assumed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H K : Ordered3Graph Nat}

theorem oneTypeBelow_prefix_congr_of_edge_columns
    (x y l : Nat) (hl : l ≤ x)
    (hX : ∀ a b : Nat, a < b → b < x →
      (H.edge a b x ↔ K.edge a b x))
    (hY : ∀ a b : Nat, a < b → b < x →
      (H.edge a b y ↔ K.edge a b y)) :
    (H.SameOneTypeBelow l x y ↔
      K.SameOneTypeBelow l x y) := by
  constructor
  · intro h a b hab hb
    calc
      K.edge a b x ↔ H.edge a b x :=
        (hX a b hab (by omega)).symm
      _ ↔ H.edge a b y := h hab hb
      _ ↔ K.edge a b y := hY a b hab (by omega)
  · intro h a b hab hb
    calc
      H.edge a b x ↔ K.edge a b x := hX a b hab (by omega)
      _ ↔ K.edge a b y := h hab hb
      _ ↔ H.edge a b y :=
        (hY a b hab (by omega)).symm

/-- First singleton meets of x with y are identical in two graphs
if the edge columns below x at x and y agree. -/
theorem oneMeet_prefix_congr_of_edge_columns
    (x y : Nat) (hxy : x < y)
    (hX : ∀ a b : Nat, a < b → b < x →
      (H.edge a b x ↔ K.edge a b x))
    (hY : ∀ a b : Nat, a < b → b < x →
      (H.edge a b y ↔ K.edge a b y)) :
    H.oneMeetLevel x y = K.oneMeetLevel x y := by
  classical
  have hH : H.oneMeetLevel x y ≤ x := by
    have hh := H.oneMeetLevel_le_min x y
    omega
  have hK : K.oneMeetLevel x y ≤ x := by
    have hh := K.oneMeetLevel_le_min x y
    omega
  apply le_antisymm
  · apply Nat.le_findGreatest (by omega)
    exact (oneTypeBelow_prefix_congr_of_edge_columns
      (H := H) (K := K) x y (H.oneMeetLevel x y)
      hH hX hY).mp (H.oneMeetLevel_agree x y)
  · apply Nat.le_findGreatest (by omega)
    exact (oneTypeBelow_prefix_congr_of_edge_columns
      (H := H) (K := K) x y (K.oneMeetLevel x y)
      hK hX hY).mpr (K.oneMeetLevel_agree x y)

/-- The mixed auxiliary type prefix is unchanged by changes to
edges whose middle coordinate is x or later. -/
theorem mixedAuxBelow_prefix_congr_of_edge_columns
    (m x y l : Nat) (hmx : m < x) (hl : l ≤ m)
    (hX : ∀ a b : Nat, a < b → b < x →
      (H.edge a b x ↔ K.edge a b x))
    (hY : ∀ a b : Nat, a < b → b < x →
      (H.edge a b y ↔ K.edge a b y)) :
    (H.SameAuxTypeBelow l m x m y ↔
      K.SameAuxTypeBelow l m x m y) := by
  constructor
  · intro h a ha
    calc
      K.edge a m x ↔ H.edge a m x :=
        (hX a m (by omega) hmx).symm
      _ ↔ H.edge a m y := h ha
      _ ↔ K.edge a m y := hY a m (by omega) hmx
  · intro h a ha
    calc
      H.edge a m x ↔ K.edge a m x := hX a m (by omega) hmx
      _ ↔ K.edge a m y := h ha
      _ ↔ H.edge a m y :=
        (hY a m (by omega) hmx).symm

/-- The literal capped auxiliary meets of (m,x),(m,y) agree
across graphs whenever the edge columns below x agree. -/
theorem mixedAuxMeet_prefix_congr_of_edge_columns
    (m x y : Nat) (hmx : m < x)
    (hX : ∀ a b : Nat, a < b → b < x →
      (H.edge a b x ↔ K.edge a b x))
    (hY : ∀ a b : Nat, a < b → b < x →
      (H.edge a b y ↔ K.edge a b y)) :
    H.auxMeetLevel m x m y = K.auxMeetLevel m x m y := by
  classical
  have hH : H.auxMeetLevel m x m y ≤ m := by
    simpa using H.auxMeetLevel_le_min m x m y
  have hK : K.auxMeetLevel m x m y ≤ m := by
    simpa using K.auxMeetLevel_le_min m x m y
  apply le_antisymm
  · apply Nat.le_findGreatest (by omega)
    exact (mixedAuxBelow_prefix_congr_of_edge_columns
      (H := H) (K := K) m x y (H.auxMeetLevel m x m y)
      hmx hH hX hY).mp (H.auxMeetLevel_agree m x m y)
  · apply Nat.le_findGreatest (by omega)
    exact (mixedAuxBelow_prefix_congr_of_edge_columns
      (H := H) (K := K) m x y (K.auxMeetLevel m x m y)
      hmx hK hX hY).mpr (K.auxMeetLevel_agree m x m y)

/-- CORE PREFIX INVARIANCE: editing edges with middle level x or
higher, while preserving all test columns ending at x and y below
x, leaves the actual LexEarlier H x y comparison unchanged. -/
theorem lexEarlier_prefix_congr_of_edge_columns
    (x y : Nat) (hxy : x < y)
    (hX : ∀ a b : Nat, a < b → b < x →
      (H.edge a b x ↔ K.edge a b x))
    (hY : ∀ a b : Nat, a < b → b < x →
      (H.edge a b y ↔ K.edge a b y)) :
    (LexEarlier H x y ↔ LexEarlier K x y) := by
  let m := H.oneMeetLevel x y
  have hMeet : K.oneMeetLevel x y = m := by
    have heq := oneMeet_prefix_congr_of_edge_columns
      (H := H) (K := K) x y hxy hX hY
    simpa only [m] using heq.symm
  have hmle : m ≤ x := by
    have hle := H.oneMeetLevel_le_min x y
    dsimp [m]
    omega
  by_cases hCap : m = x
  · have hLeft : LexEarlier H x y :=
      Or.inl ⟨hxy, by simpa only [m] using hCap⟩
    have hRight : LexEarlier K x y :=
      Or.inl ⟨hxy, by rw [hMeet]; exact hCap⟩
    exact ⟨fun _ => hRight, fun _ => hLeft⟩
  · have hmx : m < x := by omega
    have hmy : m < y := by omega
    have hAux : H.auxMeetLevel m x m y =
        K.auxMeetLevel m x m y :=
      mixedAuxMeet_prefix_congr_of_edge_columns
        (H := H) (K := K) m x y hmx hX hY
    have hq : H.auxMeetLevel m x m y < m :=
      (onePass_source_mixedAux_first_difference
        H m x y hmx hmy rfl).1
    have hH :
        LexEarlier H x y ↔
        H.edge (H.auxMeetLevel m x m y) m y :=
      onePass_lexEarlier_iff_mixedAux_right
        H m x y hmx hmy rfl
    have hK :
        LexEarlier K x y ↔
        K.edge (K.auxMeetLevel m x m y) m y :=
      onePass_lexEarlier_iff_mixedAux_right
        K m x y hmx hmy hMeet
    calc
      LexEarlier H x y ↔
          H.edge (H.auxMeetLevel m x m y) m y := hH
      _ ↔ K.edge (K.auxMeetLevel m x m y) m y := by
        rw [← hAux]
        exact hY _ m (by omega) hmx
      _ ↔ LexEarlier K x y := hK.symm

end DiaryLeafPriority
end ThreeUniformDiaries
