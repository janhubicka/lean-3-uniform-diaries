import ThreeUniformDiaries.DiaryRelativeMultiColourTailObstruction
import ThreeUniformDiaries.TwoTypeMeetLevel

/-!
# Track A: ONE complete singleton colour determines ALL new-leaf S1/S2 meets

The previous cofinal generic geometry proof separately stabilized:
  (1) singleton meets of old target leaves a with new leaves v;
  (2) full pair meets of old-old pairs (a,b) against old-new (c,v);
  (3) full pair meets of old-new pairs (a,v) against (b,v).

These THREE extra finite palette steps are not necessary when the
complete mixed singleton colour is already fixed at a cut B
DOMINATING the old target roots. Equality of the complete B-colour
of two proposed new vertices v,w means all edges to any earlier
ordered target pair x<y<B agree. The ordinary S1 and full S2
type-cut definitions then FORCE the exact numerical meet levels
with all old coordinates below B to agree.

This is a pointwise implication for arbitrary ordered 3-graphs,
not merely an existential recurrence theorem in a full RoleDiary.
It uses exact cut-maximality, not a vague ultrametric approximation.
The S1 root case requires both v,w at/above B to make its
capped first-coordinate bound identical; the two S2 pair cases
have caps fixed by the old FIRST coordinates and need no such
additional bound on v,w.

The result reduces the complete finite S1/S2 profile to ONE
pre-existing finite colour. It does NOT ensure that the colour
which genericity chooses matches the SOURCE prescribed generator
collisions, E2/E3 orientations or future order reserve, nor
produce a persistent next-leaf image or unconditional BRDs.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Equality of complete singleton B-colours preserves the
predicate that a FIXED old target vertex x has the same singleton
type as the variable new vertex, at every cut l≤B.

No bounds on x or on the new vertices v,w are necessary for this
type-level statement (only l≤B). -/
theorem sameOneTypeBelow_fixed_of_equal_singletonColour
    (K : Ordered3Graph Nat) (B x v w l : Nat)
    (hlB : l ≤ B)
    (hColour :
      DiaryLowerBoundColors.singletonColour K B v =
      DiaryLowerBoundColors.singletonColour K B w) :
    K.SameOneTypeBelow l x v ↔
      K.SameOneTypeBelow l x w := by
  constructor
  · intro hOld a b hab hbl
    have hbB : b < B := lt_of_lt_of_le hbl hlB
    exact (hOld hab hbl).trans
      (same_singletonColour_forces_same_old_pair_edge
        K B a b v w hab hbB hColour)
  · intro hNew a b hab hbl
    have hbB : b < B := lt_of_lt_of_le hbl hlB
    exact (hNew hab hbl).trans
      (same_singletonColour_forces_same_old_pair_edge
        K B a b v w hab hbB hColour).symm

/-- One complete B-colour determines the LITERAL capped S1
meet of any fixed old vertex a<B with any candidate v≥B.
No source/target RoleDiary assumption is required. -/
theorem oneMeetLevel_fixed_root_eq_of_equal_singletonColour
    (K : Ordered3Graph Nat) (B a v w : Nat)
    (haB : a < B) (hvB : B ≤ v) (hwB : B ≤ w)
    (hColour :
      DiaryLowerBoundColors.singletonColour K B v =
      DiaryLowerBoundColors.singletonColour K B w) :
    K.oneMeetLevel a v = K.oneMeetLevel a w := by
  have haV : a ≤ v := by omega
  have haW : a ≤ w := by omega
  have hBoundV : K.oneMeetLevel a v ≤ a :=
    (K.oneMeetLevel_le_min a v).trans (min_le_left _ _)
  have hBoundW : K.oneMeetLevel a w ≤ a :=
    (K.oneMeetLevel_le_min a w).trans (min_le_left _ _)
  have hVtoW :
      K.oneMeetLevel a v ≤ K.oneMeetLevel a w := by
    have hAtW : K.SameOneTypeBelow (K.oneMeetLevel a v) a w :=
      (sameOneTypeBelow_fixed_of_equal_singletonColour
        K B a v w (K.oneMeetLevel a v)
        (by omega) hColour).mp (K.oneMeetLevel_agree a v)
    exact Nat.le_findGreatest
      (le_min hBoundV (hBoundV.trans haW)) hAtW
  have hWtoV :
      K.oneMeetLevel a w ≤ K.oneMeetLevel a v := by
    have hAtV : K.SameOneTypeBelow (K.oneMeetLevel a w) a v :=
      (sameOneTypeBelow_fixed_of_equal_singletonColour
        K B a v w (K.oneMeetLevel a w)
        (by omega) hColour).mpr (K.oneMeetLevel_agree a w)
    exact Nat.le_findGreatest
      (le_min hBoundW (hBoundW.trans haV)) hAtV
  exact Nat.le_antisymm hVtoW hWtoV

/-- With fixed first pair (a,b) and fixed old first coordinate
c<B of the second pair, equality of new singleton B-colours
forces EQUALITY of the full capped S2 pair meet:
    twoMeet(a,b,c,v) = twoMeet(a,b,c,w).

This holds for all v,w, without even assuming they are ordered
above c, because the literal S2 cap depends only on a and c.
The complete colour controls the second-coordinate singleton
comparison AND the auxiliary pair incidences at every allowed
cut ≤min(a,c). -/
theorem twoMeetLevel_oldOld_newPair_eq_of_equal_singletonColour
    (K : Ordered3Graph Nat) (B a b c v w : Nat)
    (hcB : c < B)
    (hColour :
      DiaryLowerBoundColors.singletonColour K B v =
      DiaryLowerBoundColors.singletonColour K B w) :
    K.twoMeetLevel a b c v = K.twoMeetLevel a b c w := by
  have hTypes (l : Nat) (hl : l ≤ min a c) :
      K.SameTwoTypeBelow l a b c v ↔
        K.SameTwoTypeBelow l a b c w := by
    have hlB : l ≤ B := by omega
    constructor
    · rintro ⟨hFirst,hSecond,hAux⟩
      refine ⟨hFirst,
        (sameOneTypeBelow_fixed_of_equal_singletonColour
          K B b v w l hlB hColour).mp hSecond, ?_⟩
      intro z hz
      have hzc : z < c :=
        lt_of_lt_of_le hz (hl.trans (min_le_right _ _))
      exact (hAux hz).trans
        (same_singletonColour_forces_same_old_pair_edge
          K B z c v w hzc hcB hColour)
    · rintro ⟨hFirst,hSecond,hAux⟩
      refine ⟨hFirst,
        (sameOneTypeBelow_fixed_of_equal_singletonColour
          K B b v w l hlB hColour).mpr hSecond, ?_⟩
      intro z hz
      have hzc : z < c :=
        lt_of_lt_of_le hz (hl.trans (min_le_right _ _))
      exact (hAux hz).trans
        (same_singletonColour_forces_same_old_pair_edge
          K B z c v w hzc hcB hColour).symm
  apply Nat.le_antisymm
  · have hBound := K.twoMeetLevel_le_min a b c v
    have hType :=
      (hTypes (K.twoMeetLevel a b c v) hBound).mp
        (K.twoMeetLevel_agree a b c v)
    exact Nat.le_findGreatest hBound hType
  · have hBound := K.twoMeetLevel_le_min a b c w
    have hType :=
      (hTypes (K.twoMeetLevel a b c w) hBound).mpr
        (K.twoMeetLevel_agree a b c w)
    exact Nat.le_findGreatest hBound hType

/-- With fixed old first leaves a,b<B, equality of complete
singleton B-colours makes the NEW-NEW full S2 comparison
    twoMeet(a,v,b,v) = twoMeet(a,w,b,w)
literally identical. The type comparison of the repeated second
coordinate with itself is reflexive; the auxiliary comparison is
made of exactly two singleton-colour coordinates (z,a),(z,b).
No target leaf roles or numerical lower bounds on v,w are needed. -/
theorem twoMeetLevel_newNew_eq_of_equal_singletonColour
    (K : Ordered3Graph Nat) (B a b v w : Nat)
    (haB : a < B) (hbB : b < B)
    (hColour :
      DiaryLowerBoundColors.singletonColour K B v =
      DiaryLowerBoundColors.singletonColour K B w) :
    K.twoMeetLevel a v b v = K.twoMeetLevel a w b w := by
  have hTypes (l : Nat) (hl : l ≤ min a b) :
      K.SameTwoTypeBelow l a v b v ↔
        K.SameTwoTypeBelow l a w b w := by
    constructor
    · rintro ⟨hFirst,_hSelf,hAux⟩
      have hSelfW : K.SameOneTypeBelow l w w := by
        intro x y _ _
        rfl
      refine ⟨hFirst,hSelfW,?_⟩
      intro z hz
      have hza : z < a :=
        lt_of_lt_of_le hz (hl.trans (min_le_left _ _))
      have hzb : z < b :=
        lt_of_lt_of_le hz (hl.trans (min_le_right _ _))
      have hAv :=
        same_singletonColour_forces_same_old_pair_edge
          K B z a v w hza haB hColour
      have hBv :=
        same_singletonColour_forces_same_old_pair_edge
          K B z b v w hzb hbB hColour
      exact hAv.symm.trans ((hAux hz).trans hBv)
    · rintro ⟨hFirst,_hSelf,hAux⟩
      have hSelfV : K.SameOneTypeBelow l v v := by
        intro x y _ _
        rfl
      refine ⟨hFirst,hSelfV,?_⟩
      intro z hz
      have hza : z < a :=
        lt_of_lt_of_le hz (hl.trans (min_le_left _ _))
      have hzb : z < b :=
        lt_of_lt_of_le hz (hl.trans (min_le_right _ _))
      have hAv :=
        same_singletonColour_forces_same_old_pair_edge
          K B z a v w hza haB hColour
      have hBv :=
        same_singletonColour_forces_same_old_pair_edge
          K B z b v w hzb hbB hColour
      exact hAv.trans ((hAux hz).trans hBv.symm)
  apply Nat.le_antisymm
  · have hBound := K.twoMeetLevel_le_min a v b v
    have hType :=
      (hTypes (K.twoMeetLevel a v b v) hBound).mp
        (K.twoMeetLevel_agree a v b v)
    exact Nat.le_findGreatest hBound hType
  · have hBound := K.twoMeetLevel_le_min a w b w
    have hType :=
      (hTypes (K.twoMeetLevel a w b w) hBound).mpr
        (K.twoMeetLevel_agree a w b w)
    exact Nat.le_findGreatest hBound hType

end DiaryLeafPriority
end ThreeUniformDiaries
