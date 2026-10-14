import ThreeUniformDiaries.DiaryMeetUnderCloseTypes
import ThreeUniformDiaries.DiaryFullRoleDefinition
import ThreeUniformDiaries.DiaryFinitePointedATRCode
import ThreeUniformDiaries.TwoTypeMeetLevel

/-!
# Replacing one vertex of a pair by a close singleton type preserves
# the earlier auxiliary meet and lexicographic orientation

The difficult cut-zero diary orientation lemma uses a three-leaf
gadget. Its main finite calculation compares two pairs (x,y)
and (c,y), where x and c agree in singleton type through a
protected cut M and both meets with y occur no later than M.

The checked earlier-meet lemma identifies their singleton meets.
Their mixed auxiliary pair types (m,x),(m,y) and (m,c),(m,y)
agree at every cut up to m, since each edge bit z,m,x equals
the corresponding bit z,m,c. Hence the auxiliary meets and their
ordinary full pair meets coincide. The manuscript's lexicographic
predicate therefore has the same truth value on (x,y) and (c,y).

All arguments are over a general enumerated 3-hypergraph and do
not use diary edge-role markers or an extra Ramsey principle.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Replacing a vertex x by a singleton-type-equivalent vertex c
does not change the auxiliary meet of the mixed ordered pairs
(m,x),(m,y) and (m,c),(m,y), provided their common first
coordinate m occurs before the comparison cut M. -/
theorem auxMeetLevel_mixed_left_stable
    (H : Ordered3Graph Nat) (M m x c y : Nat)
    (hmM : m ≤ M)
    (hSame : H.SameOneTypeBelow (M+1) x c) :
    H.auxMeetLevel m x m y = H.auxMeetLevel m c m y := by
  classical
  have hEquiv : ∀ l, l ≤ m →
      (H.SameAuxTypeBelow l m x m y ↔
       H.SameAuxTypeBelow l m c m y) := by
    intro l hl
    constructor
    · intro h z hz
      have hzm : z < m := lt_of_lt_of_le hz hl
      have hmcut : m < M+1 := by omega
      calc
        H.edge z m c ↔ H.edge z m x :=
          (hSame (a := z) (b := m) hzm hmcut).symm
        _ ↔ H.edge z m y := h (a := z) hz
    · intro h z hz
      have hzm : z < m := lt_of_lt_of_le hz hl
      have hmcut : m < M+1 := by omega
      calc
        H.edge z m x ↔ H.edge z m c :=
          hSame (a := z) (b := m) hzm hmcut
        _ ↔ H.edge z m y := h (a := z) hz
  have hb0 : H.auxMeetLevel m x m y ≤ m := by
    simpa using H.auxMeetLevel_le_min m x m y
  have hb1 : H.auxMeetLevel m c m y ≤ m := by
    simpa using H.auxMeetLevel_le_min m c m y
  have hlo : H.auxMeetLevel m x m y ≤ H.auxMeetLevel m c m y :=
    (H.auxMeetLevel_ge_iff_sameAuxTypeBelow
      (H.auxMeetLevel m x m y) m c m y hb0 hb0).mpr
      ((hEquiv _ hb0).mp (H.auxMeetLevel_agree m x m y))
  have hhi : H.auxMeetLevel m c m y ≤ H.auxMeetLevel m x m y :=
    (H.auxMeetLevel_ge_iff_sameAuxTypeBelow
      (H.auxMeetLevel m c m y) m x m y hb1 hb1).mpr
      ((hEquiv _ hb1).mpr (H.auxMeetLevel_agree m c m y))
  exact Nat.le_antisymm hlo hhi

/-- For an early non-capped singleton meet m=x∧y, the full
ordinary meet of the mixed ordered pairs (m,x),(m,y)
equals precisely their auxiliary meet. -/
theorem twoMeetLevel_mixed_eq_aux
    (H : Ordered3Graph Nat) (m x y : Nat)
    (hmx : m < x) (hmy : m < y)
    (hmeet : H.oneMeetLevel x y = m) :
    H.twoMeetLevel m x m y = H.auxMeetLevel m x m y := by
  have hbound : H.auxMeetLevel m x m y ≤ m := by
    simpa using H.auxMeetLevel_le_min m x m y
  calc
    H.twoMeetLevel m x m y =
      min (H.auxMeetLevel m x m y)
        (min (H.oneMeetLevel m m) (H.oneMeetLevel x y)) :=
          H.twoMeetLevel_eq_min m x m y hmx hmy
    _ = H.auxMeetLevel m x m y := by
      simp [oneMeetLevel_self_full, hmeet, hbound]

/-- Two pairs with one common second vertex have the same
lexicographic precedence whenever their non-capped singleton
meets and the mixed full pair meets agree. -/
theorem lexEarlier_iff_of_same_mixed_meets
    (H : Ordered3Graph Nat) (m x c y : Nat)
    (hmx : m < x) (hmc : m < c) (hmy : m < y)
    (hxy : H.oneMeetLevel x y = m)
    (hcy : H.oneMeetLevel c y = m)
    (hMixed : H.twoMeetLevel m x m y =
      H.twoMeetLevel m c m y) :
    (DiaryLeafPriority.LexEarlier H x y ↔
      DiaryLeafPriority.LexEarlier H c y) := by
  have hxyMin : m < min x y := by omega
  have hcyMin : m < min c y := by omega
  have hxn : m ≠ x := by omega
  have hcn : m ≠ c := by omega
  simp [DiaryLeafPriority.LexEarlier, hxy, hcy,
    hxyMin, hcyMin, hxn, hcn, hMixed]

/-- Main orientation replacement lemma: if x,c have the same
singleton type through cut M, all three vertices lie strictly
after M, and the pair (x,y) already split by M, then the
lexicographic orientations of (x,y) and (c,y) coincide.
Neither pair need have its vertices in the same numerical order. -/
theorem lexEarlier_stable_under_close_one_types
    (H : Ordered3Graph Nat) (M x y c : Nat)
    (hMx : M < x) (hMy : M < y) (hMc : M < c)
    (hSame : H.SameOneTypeBelow (M+1) x c)
    (hMeet : H.oneMeetLevel x y ≤ M) :
    (DiaryLeafPriority.LexEarlier H x y ↔
      DiaryLeafPriority.LexEarlier H c y) := by
  let m := H.oneMeetLevel x y
  have hmx : m < x := by dsimp [m]; omega
  have hmy : m < y := by dsimp [m]; omega
  have hmc : m < c := by dsimp [m]; omega
  have hmM : m ≤ M := hMeet
  have hcy : H.oneMeetLevel c y = m :=
    H.oneMeetLevel_stable_under_close_one_types
      M x y c hMx hMy hMc hSame hMeet
  have hAux : H.auxMeetLevel m x m y =
      H.auxMeetLevel m c m y :=
    H.auxMeetLevel_mixed_left_stable M m x c y hmM hSame
  have hTwo : H.twoMeetLevel m x m y =
      H.twoMeetLevel m c m y := by
    calc
      H.twoMeetLevel m x m y =
        H.auxMeetLevel m x m y :=
          H.twoMeetLevel_mixed_eq_aux m x y hmx hmy rfl
      _ = H.auxMeetLevel m c m y := hAux
      _ = H.twoMeetLevel m c m y :=
        (H.twoMeetLevel_mixed_eq_aux m c y hmc hmy hcy).symm
  exact H.lexEarlier_iff_of_same_mixed_meets
    m x c y hmx hmc hmy rfl hcy hTwo

end Ordered3Graph
end ThreeUniformDiaries
