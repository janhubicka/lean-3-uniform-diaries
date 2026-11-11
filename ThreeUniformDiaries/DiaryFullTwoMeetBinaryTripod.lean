import ThreeUniformDiaries.DiaryTwoSplitWitnessClasses

/-!
# Track D: full S2 meets have a binary tripod geometry

Full pair-type agreement at each cut is an equivalence relation. Thus
the capped numerical S2 meet satisfies the usual ultrametric
three-pair minimum inequality, without any role hypotheses.

For genuine two-split meetings in a full diary, V2 excludes an
equilateral triple: the three pair incidences at one common split
would have to be pairwise opposite Boolean values. Combining the
inequality with this obstruction yields the STRICT BINARY TRIPOD:
among three genuine high S2 pairwise meets, two equal the minimum
and the remaining meet is strictly larger.

This is a structural necessary constraint on any finite generator
table. It is NOT an existence theorem for a prescribed finite
relative support, a generic tail, or a persistent successor.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Transitivity of full pair types implies an ultrametric-style
minimum bound for the exact capped full S2 meet. The cap at the
lesser first coordinate is preserved without any diary axioms. -/
theorem twoMeetLevel_min_trans
    (K : Ordered3Graph Nat) (a b c d e f : Nat) :
    min (K.twoMeetLevel a b c d) (K.twoMeetLevel c d e f) ≤
      K.twoMeetLevel a b e f := by
  let t := min (K.twoMeetLevel a b c d)
    (K.twoMeetLevel c d e f)
  have htAB : t ≤ K.twoMeetLevel a b c d := min_le_left _ _
  have htBC : t ≤ K.twoMeetLevel c d e f := min_le_right _ _
  have hAB : K.SameTwoTypeBelow t a b c d :=
    K.sameTwoTypeBelow_mono t (K.twoMeetLevel a b c d)
      a b c d htAB (K.twoMeetLevel_agree a b c d)
  have hBC : K.SameTwoTypeBelow t c d e f :=
    K.sameTwoTypeBelow_mono t (K.twoMeetLevel c d e f)
      c d e f htBC (K.twoMeetLevel_agree c d e f)
  have hAE : K.SameTwoTypeBelow t a b e f :=
    K.sameTwoTypeBelow_trans t a b c d e f hAB hBC
  have htA : t ≤ a :=
    htAB.trans ((K.twoMeetLevel_le_min a b c d).trans
      (min_le_left _ _))
  have htE : t ≤ e :=
    htBC.trans ((K.twoMeetLevel_le_min c d e f).trans
      (min_le_right _ _))
  exact (K.twoMeetLevel_ge_iff_sameTwoTypeBelow
    t a b e f htA htE).mpr hAE

end Ordered3Graph

namespace DiaryLeafPriority

/-- Three ordered pairs cannot ALL meet each other at the SAME
genuine two-split s, strictly below their first members. At s
the V2 witness law makes all three Boolean E3 bits pairwise
different, impossible for a two-element palette.

No separate leaf-role assumptions on a,b,c,d,e,f are required;
the three genuine S2 meet identities are already supplied. -/
theorem RoleDiary.no_three_pairwise_two_meets_at_split
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (s a b c d e f : Nat)
    (hs : IsTwoSplit K s)
    (hsa : s < a) (hsc : s < c) (hse : s < e)
    (hAC : K.twoMeetLevel a b c d = s)
    (hAE : K.twoMeetLevel a b e f = s)
    (hCE : K.twoMeetLevel c d e f = s) : False := by
  have h01 : ¬ (K.edge s a b ↔ K.edge s c d) :=
    DK.twoSplit_witness_opposite_incidence s a b c d
      hs hsa hsc hAC
  have h02 : ¬ (K.edge s a b ↔ K.edge s e f) :=
    DK.twoSplit_witness_opposite_incidence s a b e f
      hs hsa hse hAE
  have h12 : ¬ (K.edge s c d ↔ K.edge s e f) :=
    DK.twoSplit_witness_opposite_incidence s c d e f
      hs hsc hse hCE
  tauto

/-- Binary tripod law for full ordered-pair meets. If the first
members a,c,e are genuine leaves and ALL THREE pairwise full
S2 meets are genuine two-splits, the smallest numerical meet
occurs exactly twice, with the remaining meet STRICTLY higher.

The ordered pairs need not come from an induced generic copy.
No preassigned branch signs or nonleaf images are constructed. -/
theorem RoleDiary.genuine_twoMeet_binary_tripod
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (a b c d e f : Nat)
    (ha : IsLeaf K a) (hc : IsLeaf K c) (he : IsLeaf K e)
    (hAC : IsTwoSplit K (K.twoMeetLevel a b c d))
    (hAE : IsTwoSplit K (K.twoMeetLevel a b e f))
    (hCE : IsTwoSplit K (K.twoMeetLevel c d e f)) :
    (let x := K.twoMeetLevel a b c d
     let y := K.twoMeetLevel a b e f
     let z := K.twoMeetLevel c d e f
     (x = y ∧ x < z) ∨
       (x = z ∧ x < y) ∨
       (y = z ∧ y < x)) := by
  let x := K.twoMeetLevel a b c d
  let y := K.twoMeetLevel a b e f
  let z := K.twoMeetLevel c d e f
  have hNoAll : ¬ (x = y ∧ y = z) := by
    rintro ⟨hxy, hyz⟩
    have hxA : x ≤ a :=
      (K.twoMeetLevel_le_min a b c d).trans (min_le_left _ _)
    have hxC : x ≤ c :=
      (K.twoMeetLevel_le_min a b c d).trans (min_le_right _ _)
    have hyE : y ≤ e :=
      (K.twoMeetLevel_le_min a b e f).trans (min_le_right _ _)
    have hxE : x ≤ e := by omega
    have hxneA : x ≠ a := by
      intro hEq
      have hBad : IsTwoSplit K a := hEq ▸ hAC
      exact ha.2.2 hBad.2.2
    have hxneC : x ≠ c := by
      intro hEq
      have hBad : IsTwoSplit K c := hEq ▸ hAC
      exact hc.2.2 hBad.2.2
    have hxneE : x ≠ e := by
      intro hEq
      have hBad : IsTwoSplit K e := hEq ▸ hAC
      exact he.2.2 hBad.2.2
    have hxa : x < a := by omega
    have hxc : x < c := by omega
    have hxe : x < e := by omega
    have hYEq : K.twoMeetLevel a b e f = x := hxy.symm
    have hZEq : K.twoMeetLevel c d e f = x :=
      hyz.symm.trans hxy.symm
    exact DK.no_three_pairwise_two_meets_at_split
      x a b c d e f hAC hxa hxc hxe rfl hYEq hZEq
  have hXZleY : min x z ≤ y :=
    K.twoMeetLevel_min_trans a b c d e f
  have hYZleX : min y z ≤ x := by
    have h := K.twoMeetLevel_min_trans a b e f c d
    change min y (K.twoMeetLevel e f c d) ≤ x at h
    rw [K.twoMeetLevel_comm e f c d] at h
    exact h
  have hXYleZ : min x y ≤ z := by
    have h := K.twoMeetLevel_min_trans c d a b e f
    change min (K.twoMeetLevel c d a b) y ≤ z at h
    rw [K.twoMeetLevel_comm c d a b] at h
    exact h
  change (x = y ∧ x < z) ∨
    (x = z ∧ x < y) ∨ (y = z ∧ y < x)
  rcases lt_trichotomy x y with hxy | heq | hyx
  · have hxleZ : x ≤ z := by
      simpa only [min_eq_left hxy.le] using hXYleZ
    have hzleX : z ≤ x := by
      by_contra hBad
      have hxltZ : x < z := Nat.lt_of_not_ge hBad
      have hMinGt : x < min y z := lt_min hxy hxltZ
      exact (not_lt_of_ge hYZleX) hMinGt
    exact Or.inr (Or.inl
      ⟨le_antisymm hxleZ hzleX, hxy⟩)
  · have hxleZ : x ≤ z := by
      simpa only [heq, min_self] using hXYleZ
    by_cases hxltZ : x < z
    · exact Or.inl ⟨heq, hxltZ⟩
    · have hxEqZ : x = z :=
        le_antisymm hxleZ (Nat.le_of_not_gt hxltZ)
      have hAll : x = y ∧ y = z :=
        ⟨heq, heq.symm.trans hxEqZ⟩
      exact False.elim (hNoAll hAll)
  · have hyleZ : y ≤ z := by
      simpa only [min_eq_right hyx.le] using hXYleZ
    have hzleY : z ≤ y := by
      by_contra hBad
      have hyltZ : y < z := Nat.lt_of_not_ge hBad
      have hMinGt : y < min x z := lt_min hyx hyltZ
      exact (not_lt_of_ge hXZleY) hMinGt
    exact Or.inr (Or.inr
      ⟨le_antisymm hyleZ hzleY, hyx⟩)

end DiaryLeafPriority
end ThreeUniformDiaries
