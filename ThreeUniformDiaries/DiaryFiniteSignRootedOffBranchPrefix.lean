import ThreeUniformDiaries.DiaryFiniteSignRootedCrossMarkerExtension

/-!
# Off-branch classification is determined by a shared sign-rooted prefix

The sign-rooted raw tree has a prefix-unique parent at every
earlier level. If Y lies below a source cut s and two branches
agree on their node at s, then Y belongs to the prefix of
the first branch precisely when it belongs to the prefix of
the second. For later leaves U,V of those respective branches,
the off-branch condition for (Y,U) and (Y,V) is identical.

This is the key geometric fact permitting a prefix-uniform
orientation of missing cross-branch Devlin markers to preserve
the raw V1/V2 predecessor profiles. It is independent of
arbitrary choices of the marker orientation. It does NOT
assert that such a choice satisfies literal V3.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace FiniteSignRootedFlipFamily

variable {A : Ordered3Graph Nat} {n : Nat} {ι : Type*}

/-- A raw node Y earlier than a branch terminal is paired with
that terminal on some original branch iff Y is exactly the
corresponding earlier node of the chosen terminal's branch. -/
theorem sharedBranchPair_with_terminal_iff_prefix
    (F : FiniteSignRootedFlipFamily A n ι)
    (i : ι) (Y : FiniteSignRootedNode A n)
    (z : Nat) (hYz : Y.1 < z) (hzn : z < n) :
    F.SharedBranchPair Y (F.node i z) ↔
      Y = F.node i Y.1 := by
  constructor
  · rintro ⟨j,y,w,hyw,hwn,hY,hZ⟩
    have hwz : w = z := by
      have hh := congrArg Prod.fst hZ
      simpa only [F.node_level] using hh
    have hyY : y = Y.1 := by
      have hh := congrArg Prod.fst hY
      simpa only [F.node_level] using hh
    rw [hwz] at hZ
    have hPrefix : F.node j y = F.node i y :=
      F.node_prefix_eq_of_terminal_eq j i y z
        (by omega) hZ
    calc
      Y = F.node j y := hY.symm
      _ = F.node i y := hPrefix
      _ = F.node i Y.1 := by rw [hyY]
  · intro h
    exact ⟨i,Y.1,z,hYz,hzn,h.symm,rfl⟩

/-- Two branches sharing a cut s have identical earlier
prefix nodes, including an off-branch earlier node's LEVEL. -/
theorem earlier_node_eq_of_shared_cut
    (F : FiniteSignRootedFlipFamily A n ι)
    (i j : ι) (s : Nat)
    (hShared : F.node i s = F.node j s)
    (Y : FiniteSignRootedNode A n)
    (hYs : Y.1 < s) :
    F.node i Y.1 = F.node j Y.1 :=
  F.node_prefix_eq_of_terminal_eq i j Y.1 s
    hYs.le hShared

/-- For any earlier raw node Y and later SOURCE leaves u,v
on branches sharing their node at cut s, an ordered pair
(Y,U) is off-branch iff (Y,V) is off-branch.

No assumption of positivity at s is needed. This is strictly
a structural fact about the sign-rooted raw prefix geometry. -/
theorem offBranchLeafPair_iff_of_shared_cut
    (F : FiniteSignRootedFlipFamily A n ι)
    (i j : ι) (s : Nat)
    (hShared : F.node i s = F.node j s)
    (Y : FiniteSignRootedNode A n)
    (hYs : Y.1 < s)
    (u v : Nat) (hsu : s ≤ u) (hsv : s ≤ v)
    (hun : u < n) (hvn : v < n)
    (hu : IsLeaf A u) (hv : IsLeaf A v) :
    F.OffBranchLeafPair Y (F.node i u) ↔
      F.OffBranchLeafPair Y (F.node j v) := by
  have hPrefix := F.earlier_node_eq_of_shared_cut
    i j s hShared Y hYs
  have hI := F.sharedBranchPair_with_terminal_iff_prefix
    i Y u (by omega) hun
  have hJ := F.sharedBranchPair_with_terminal_iff_prefix
    j Y v (by omega) hvn
  constructor
  · intro h
    refine ⟨h.leafY, ?_, ?_, ?_⟩
    · simpa only [F.node_level] using hv
    · simpa only [F.node_level] using
        (show Y.1 < v by omega)
    · intro hSharedJ
      have hYJ : Y = F.node j Y.1 := hJ.mp hSharedJ
      have hYI : Y = F.node i Y.1 := hYJ.trans hPrefix.symm
      exact h.separated (hI.mpr hYI)
  · intro h
    refine ⟨h.leafY, ?_, ?_, ?_⟩
    · simpa only [F.node_level] using hu
    · simpa only [F.node_level] using
        (show Y.1 < u by omega)
    · intro hSharedI
      have hYI : Y = F.node i Y.1 := hI.mp hSharedI
      have hYJ : Y = F.node j Y.1 := hYI.trans hPrefix
      exact h.separated (hJ.mpr hYJ)

/-- A prefix-uniform orientation assigns equal cross-marker
choices when comparing an earlier raw node Y with two later
source leaves on branches sharing the source cut s.
This is a sufficient stability condition, NOT the full V3
lexicographic coherence condition. -/
def PrefixUniformOrientation
    (F : FiniteSignRootedFlipFamily A n ι)
    (orient : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop) : Prop :=
  ∀ i j : ι, ∀ s : Nat,
    F.node i s = F.node j s →
    ∀ (Y : FiniteSignRootedNode A n) (u v : Nat),
      Y.1 < s → s ≤ u → s ≤ v → u < n → v < n →
      IsLeaf A Y.1 → IsLeaf A u → IsLeaf A v →
      (orient Y (F.node i u) ↔ orient Y (F.node j v))

/-- The prefix-uniformity condition itself is consistent:
a constant marker orientation witnesses it. This does NOT
prove that the constant choice is a valid diary V3 orientation. -/
theorem exists_prefixUniformOrientation
    (F : FiniteSignRootedFlipFamily A n ι) :
    ∃ orient : FiniteSignRootedNode A n →
        FiniteSignRootedNode A n → Prop,
      F.PrefixUniformOrientation orient := by
  refine ⟨(fun _ _ => True), ?_⟩
  intro i j s hShared Y u v hYs hsu hsv hun hvn hLeafY hu hv
  exact Iff.rfl

end FiniteSignRootedFlipFamily
end DiaryLeafPriority
end ThreeUniformDiaries
