import ThreeUniformDiaries.DiaryGenericFiniteOldSupportUnboundedNextLeaf
import ThreeUniformDiaries.DiaryInfiniteHighOneSplitCone

/-!
# Track D: arbitrarily deep S1 cones of genuinely reserved next leaves
# over ONE COMPLETE chosen old finite diary support

The verified generic finite-old-set avoidance / finite unavoidability
argument gives some whole old reserved support f:S_m->K with genuinely
reserved next-leaf images arbitrarily far out in an arbitrary
prescribed unordered induced generic leaf range.

Choose a numerically increasing sequence of ACTUAL next-leaf images
from this cofinal supply, retaining their complete reserved support
maps and literal compatibility with f. The previously CI-verified
infinite high S1 cone theorem then refines this sequence into a
subsequence of an arbitrary high singleton-type cone.

The resulting candidate leaf values are numerical STRICTLY increasing,
all are actual old-compatible reserved next-stage images, all have
the SAME full old S_m support f, and every distinct pair has a
GENUINE S1 split meet above an arbitrary cutoff B and the SAME
complete mixed singleton colour below B.

This is a positive UNBOUNDED IMMEDIATE successor reservoir for
EVERY new source leaf m with a nonempty earlier leaf prefix.
It does NOT give a next image that survives all future source
horizons, an induced generic subcopy inside the chosen candidate
set, or countable unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- In the original unordered generic leaf range, one may choose
ONE whole old reserved support map f and infinitely many strictly
target-value-increasing next-leaf images v_k at arbitrary depth B.

Each v_k has its OWN complete actual reserved source-support stage
g_k at m+1, compatible with exactly the SAME old support f.
Every two distinct v_k have equal complete singleton colour at B
and a genuine S1 meet at least B. No compatibility of the g_k at
later horizons is asserted, and f is chosen rather than prescribed. -/
theorem RoleDiary.exists_complete_old_support_with_deep_reserved_next_leaf_cone
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (m : Nat) (hm : IsLeaf H m)
    (hOldNonempty : (countableDiaryLeafPrefix H m).Nonempty)
    (B M : Nat) :
    ∃ f : Nat → Nat,
      ReservedDiaryStage H K (fun t : Nat => F t) m f ∧
      ∃ values : Nat → Nat,
        StrictMono values ∧
        (∀ k : Nat,
          M < values k ∧
          ∃ t : Nat, ∃ g : Nat → Nat,
            values k = F t ∧
            ReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g ∧
            CofinalDiaryStageCompatible H m f g ∧
            g m = values k) ∧
        (∀ i j : Nat, i < j →
          DiaryLowerBoundColors.singletonColour K B (values i) =
            DiaryLowerBoundColors.singletonColour K B (values j) ∧
          IsOneSplit K (K.oneMeetLevel (values i) (values j)) ∧
          B ≤ K.oneMeetLevel (values i) (values j)) := by
  classical
  obtain ⟨f,Pf,hCofinal⟩ :=
    DH.exists_some_fixed_old_support_with_unbounded_reserved_next_leaf
      DK G F hFLeaf m hm hOldNonempty
  have hValid (X : Nat) :
      ∃ v : Nat, X < v ∧ IsLeaf K v ∧
        ∃ t : Nat, ∃ g : Nat → Nat,
          v = F t ∧
          ReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g ∧
          CofinalDiaryStageCompatible H m f g ∧
          g m = v := by
    obtain ⟨t,g,hHigh,Q,hOld,hNew⟩ := hCofinal X
    exact ⟨F t,hHigh,hFLeaf t,t,g,rfl,Q,hOld,hNew⟩
  let pick : Nat → Nat := fun X => Classical.choose (hValid X)
  have hPick (X : Nat) :
      X < pick X ∧ IsLeaf K (pick X) ∧
      ∃ t : Nat, ∃ g : Nat → Nat,
        pick X = F t ∧
        ReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g ∧
        CofinalDiaryStageCompatible H m f g ∧
        g m = pick X := by
    exact Classical.choose_spec (hValid X)
  let raw : Nat → Nat :=
    Nat.rec (pick (max M B)) (fun _ prev => pick prev)
  have hRawStep (k : Nat) : raw k < raw (k + 1) := by
    change raw k < pick (raw k)
    exact (hPick (raw k)).1
  have hRawMono : StrictMono raw :=
    strictMono_nat_of_lt_succ hRawStep
  have hRawGood (k : Nat) :
      IsLeaf K (raw k) ∧
      ∃ t : Nat, ∃ g : Nat → Nat,
        raw k = F t ∧
        ReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g ∧
        CofinalDiaryStageCompatible H m f g ∧
        g m = raw k := by
    cases k with
    | zero =>
        change IsLeaf K (pick (max M B)) ∧
          ∃ t : Nat, ∃ g : Nat → Nat,
            pick (max M B) = F t ∧
            ReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g ∧
            CofinalDiaryStageCompatible H m f g ∧
            g m = pick (max M B)
        exact (hPick (max M B)).2
    | succ k =>
        change IsLeaf K (pick (raw k)) ∧
          ∃ t : Nat, ∃ g : Nat → Nat,
            pick (raw k) = F t ∧
            ReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g ∧
            CofinalDiaryStageCompatible H m f g ∧
            g m = pick (raw k)
        exact (hPick (raw k)).2
  have hRawLeaf (k : Nat) : IsLeaf K (raw k) :=
    (hRawGood k).1
  obtain ⟨indices,hIndicesMono,hProperties,hPairs⟩ :=
    DK.exists_infinite_high_oneSplit_cone
      raw hRawMono.injective hRawLeaf B M 0
  let values : Nat → Nat := fun k => raw (indices k)
  have hValuesMono : StrictMono values := by
    intro i j hij
    exact hRawMono (hIndicesMono hij)
  refine ⟨f,Pf,values,hValuesMono,?_,?_⟩
  · intro k
    have hHigh : M < values k := (hProperties k).2.1
    obtain ⟨_hLeaf,t,g,hEq,Q,hOld,hNew⟩ :=
      hRawGood (indices k)
    exact ⟨hHigh,t,g,hEq,Q,hOld,hNew⟩
  · intro i j hij
    exact hPairs i j hij

end DiaryLeafPriority
end ThreeUniformDiaries
