import ThreeUniformDiaries.DiaryFiniteCanonicalRankedOffBranchMask

/-!
# Same-branch causal marker masks agree before arbitrary source cuts

The existing mask-coherence theorem handles an earlier rank cut
when its source vertex is a 1- or 2-split. This is sufficient for
global V1/V2 and exact old split witnesses, but it does NOT cover
a cap at the source level of a LEAF.

For two later source leaves on one original flip branch, we prove
that their off-branch marker masks agree at every raw predecessor
of ANY earlier branch node s, regardless of the role of s.

At strictly smaller original source levels, the existing prefix
lemma applies. If a different node Y at the SAME source level s
occurs earlier in the total rank order, then it lies off the
chosen original branch. If Y is itself a leaf, its marker pair
with EACH later branch terminal is selected; if Y is not a
leaf, neither pair is selected. Thus the two masks agree even
for same-level ties, unlike the split-only proof where both
masks vanish.

Rank surjectivity transports this equality to every numerical
predecessor of the genuine finite source vertex. This is the
new causal input needed for possible capped full pair meets
whose first source coordinate is itself a leaf. It does not
assert that all such numerical meets are already protected.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace FiniteSignRootedFlipFamily

variable {A : Ordered3Graph Nat} {n : Nat} {ι : Type*}

/-- An arbitrary common source-branch node s gives the same
ordered off-branch mask against any TWO strictly later leaves
of that branch at every predecessor in the level-first order.
No requirement that s is a split; s may itself be a leaf. -/
theorem orderedOffBranch_sameBranch_rank_predecessor
    (F : FiniteSignRootedFlipFamily A n ι)
    (before : FiniteSignRootedNode A n →
      FiniteSignRootedNode A n → Prop)
    (hLevel : F.ExtendsSourceLevels before)
    (hOrder : F.LevelFirstStrictOrder before)
    (i : ι) (s u v : Nat)
    (hsu : s < u) (hsv : s < v)
    (hun : u < n) (hvn : v < n)
    (hu : IsLeaf A u) (hv : IsLeaf A v)
    (Y : FiniteSignRootedNode A n)
    (hYS : before Y (F.node i s)) :
    F.OrderedOffBranchLeafPair before Y (F.node i u) ↔
      F.OrderedOffBranchLeafPair before Y (F.node i v) := by
  have hYle : Y.1 ≤ s := by
    have h := hOrder.1 Y (F.node i s) hYS
    simpa only [F.node_level] using h
  rcases lt_or_eq_of_le hYle with hYlt | hYeq
  · exact F.orderedOffBranch_sharedCut_of_source_lt
      before hLevel i i s u v rfl
      hsu.le hsv.le hun hvn hu hv Y hYlt
  · have hNe : Y ≠ F.node i s := by
      intro hEq
      have hLoop : before (F.node i s) (F.node i s) := by
        simpa only [hEq] using hYS
      exact (hOrder.2 (F.node i s)) hLoop
    have hYU : Y.1 < (F.node i u).1 := by
      simp only [F.node_level]
      omega
    have hYV : Y.1 < (F.node i v).1 := by
      simp only [F.node_level]
      omega
    have hSeparatedU :
        ¬ F.SharedBranchPair Y (F.node i u) := by
      intro hShared
      have hOn := (F.sharedBranchPair_with_terminal_iff_prefix
        i Y u hYU hun).mp hShared
      exact hNe (by simpa only [hYeq] using hOn)
    have hSeparatedV :
        ¬ F.SharedBranchPair Y (F.node i v) := by
      intro hShared
      have hOn := (F.sharedBranchPair_with_terminal_iff_prefix
        i Y v hYV hvn).mp hShared
      exact hNe (by simpa only [hYeq] using hOn)
    by_cases hLeafY : IsLeaf A Y.1
    · have hOffU : F.OrderedOffBranchLeafPair
          before Y (F.node i u) :=
        ⟨hLeafY, hu, hLevel Y (F.node i u) hYU, hSeparatedU⟩
      have hOffV : F.OrderedOffBranchLeafPair
          before Y (F.node i v) :=
        ⟨hLeafY, hv, hLevel Y (F.node i v) hYV, hSeparatedV⟩
      exact ⟨fun _ => hOffV, fun _ => hOffU⟩
    · exact iff_of_false
        (fun h => hLeafY h.leafY)
        (fun h => hLeafY h.leafY)

end FiniteSignRootedFlipFamily

/-- The ACTUAL Nat-indexed off-branch mask agrees on two later
source leaves of the same canonical flip below the numerical
rank of any earlier node s, including when s has LEAF role. -/
theorem finiteCanonicalRankedOffBranchMask_sameBranch_below
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (i : FiniteCanonicalFlipIndex A n)
    (s u v : Nat)
    (hsn : s < n) (hsu : s < u) (hsv : s < v)
    (hun : u < n) (hvn : v < n)
    (hu : IsLeaf A u) (hv : IsLeaf A v) :
    SameEarlierMarkerMask
      (finiteCanonicalRankedOffBranchMask DA)
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i s hsn)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i u hun)).val
      (finiteCanonicalNodeIndex DA
        (finiteCanonicalNodeAt DA i v hvn)).val := by
  classical
  let F := finiteCanonicalSignRootedFamily DA
  let S := finiteCanonicalNodeAt DA i s hsn
  intro k hk
  have hkCard : k < Fintype.card
      (FiniteCanonicalSignRootedVertex DA) :=
    lt_trans hk (finiteCanonicalNodeIndex DA S).isLt
  obtain ⟨Y,hY⟩ := finiteCanonicalNodeIndex_surjective DA
    (⟨k,hkCard⟩ :
      Fin (Fintype.card (FiniteCanonicalSignRootedVertex DA)))
  have hkRank : (finiteCanonicalNodeIndex DA Y).val = k :=
    congrArg Fin.val hY
  have hBefore :
      finiteCanonicalNodeBefore DA Y S :=
    (finiteCanonicalNodeBefore_iff_rank_lt DA Y S).mpr (by
      simpa only [hkRank,S] using hk)
  have hAmbient : finiteCanonicalNodeBeforeAmbient DA Y.val
      (F.node i s) :=
    (finiteCanonicalNodeBefore_iff_ambient DA Y S).mp hBefore
  have hRaw := F.orderedOffBranch_sameBranch_rank_predecessor
    (finiteCanonicalNodeBeforeAmbient DA)
    (finiteCanonicalNodeBeforeAmbient_extends_levels DA)
    (finiteCanonicalNodeBeforeAmbient_levelFirstStrictOrder DA)
    i s u v hsu hsv hun hvn hu hv Y.val hAmbient
  have hRanked :=
    (finiteCanonicalRankedOffBranchMask_iff DA Y
      (finiteCanonicalNodeAt DA i u hun)).trans
      (hRaw.trans
        (finiteCanonicalRankedOffBranchMask_iff DA Y
          (finiteCanonicalNodeAt DA i v hvn)).symm)
  simpa only [hkRank] using hRanked

end DiaryLeafPriority
end ThreeUniformDiaries
