import ThreeUniformDiaries.DiarySecondLeafCofinalRootedSplitCriterion
import ThreeUniformDiaries.DiaryInfiniteHighOneSplitCone

/-!
# Track D: deep S1 cones of ACTUAL rooted reserved second-leaf successors

Fix a valid one-leaf old reserved stage and a single target one-split
s below its literally fixed old target leaf w=f(a). Suppose the
prescribed F-range contains arbitrarily high actual target leaves
with exact oneMeet(w,v)=s, and s passes the source-required right E2
polarity and two finite numerical gap checks.

The verified exact rooted second-leaf iff gives arbitrarily high
genuine RESERVED successor maps at this SAME s, fixing the old a.
Choose strictly numerically increasing successor leaf values by
recursion. Apply the verified infinite-high-S1-cone theorem to those
actual successor images (not to the entire F-range).

Consequently, for every B,M there is an INFINITE strictly increasing
sequence of genuine reserved second-leaf images v_k>M, all with exact
oneMeet(w,v_k)=s, and every pair v_i,v_j has a genuine one-split
meet at least B. Each v_k has its OWN complete actual old-compatible
reserved successor witness; no synthetic candidate or false
coherence among those maps is assumed.

This is a positive rooted DEEP immediate-successor reservoir.
It does not assert that any one such successor extends to all
future finite horizons; no third-leaf E3/E5 target profile is built.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A favourable cofinal E2 split fibre supports a countably infinite
TARGET-NUMERICALLY strictly increasing sequence of genuinely valid
reserved second-source-leaf images. Their pairwise S1 meets are
arbitrarily high, although every candidate meets the fixed old leaf
w at the SAME (possibly much lower) chosen split s.

All selected successor maps independently preserve their old source
leaf a, full induced edges/nonedges, roles, source meets and future
order reserve. The maps are NOT claimed mutually coherent in later
source horizons, nor is any persistent candidate constructed. -/
theorem RoleDiary.second_leaf_favourable_split_has_deep_reserved_cone
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (F f : Nat → Nat) (a m s : Nat)
    (ha : IsLeaf H a) (hm : IsLeaf H m) (ham : a < m)
    (hOld : countableDiaryLeafPrefix H m = {a})
    (P : ReservedDiaryStage H K F m f)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (hsRole : IsOneSplit K s) (hsBelow : s < f a)
    (hCone : ∀ M : Nat, ∃ t : Nat,
      M < F t ∧ K.oneMeetLevel (f a) (F t) = s)
    (hBit : H.edge 0 (H.oneMeetLevel a m) m ↔
      ¬ K.edge 0 s (f a))
    (hGap1 : H.oneMeetLevel a m ≤ s)
    (hGap2 : s + (a - H.oneMeetLevel a m) ≤ f a)
    (B M : Nat) :
    ∃ values : Nat → Nat,
      StrictMono values ∧
      (∀ k : Nat,
        M < values k ∧
        K.oneMeetLevel (f a) (values k) = s ∧
        ∃ t : Nat, ∃ g : Nat → Nat,
          values k = F t ∧
          ReservedDiaryStage H K F (m + 1) g ∧
          (∀ u : Nat, u ∈ countableDiaryLeafPrefix H m →
            g u = f u) ∧
          g m = values k) ∧
      (∀ i j : Nat, i < j →
        IsOneSplit K (K.oneMeetLevel (values i) (values j)) ∧
        B ≤ K.oneMeetLevel (values i) (values j)) := by
  classical
  have hValid (X : Nat) :
      ∃ v : Nat,
        X < v ∧
        K.oneMeetLevel (f a) v = s ∧
        ∃ t : Nat, ∃ g : Nat → Nat,
          v = F t ∧
          ReservedDiaryStage H K F (m + 1) g ∧
          (∀ u : Nat, u ∈ countableDiaryLeafPrefix H m →
            g u = f u) ∧
          g m = v := by
    obtain ⟨t,g,hHigh,hMeet,Q,hKeep,hNew⟩ :=
      DH.second_leaf_cofinal_successors_of_rooted_split_fibre
        DK F f a m s ha hm ham hOld P hFLeaf
        hsRole hsBelow hCone hBit hGap1 hGap2 X
    exact ⟨F t,hHigh,hMeet,t,g,rfl,Q,hKeep,hNew⟩
  let pick : Nat → Nat := fun X => Classical.choose (hValid X)
  have hPick (X : Nat) :
      X < pick X ∧
      K.oneMeetLevel (f a) (pick X) = s ∧
      ∃ t : Nat, ∃ g : Nat → Nat,
        pick X = F t ∧
        ReservedDiaryStage H K F (m + 1) g ∧
        (∀ u : Nat, u ∈ countableDiaryLeafPrefix H m →
          g u = f u) ∧
        g m = pick X := by
    exact Classical.choose_spec (hValid X)
  let raw : Nat → Nat :=
    Nat.rec (pick (max M (f a))) (fun _ prev => pick prev)
  have hStep (k : Nat) : raw k < raw (k + 1) := by
    change raw k < pick (raw k)
    exact (hPick (raw k)).1
  have hRawMono : StrictMono raw :=
    strictMono_nat_of_lt_succ hStep
  have hRawGood (k : Nat) :
      K.oneMeetLevel (f a) (raw k) = s ∧
      ∃ t : Nat, ∃ g : Nat → Nat,
        raw k = F t ∧
        ReservedDiaryStage H K F (m + 1) g ∧
        (∀ u : Nat, u ∈ countableDiaryLeafPrefix H m →
          g u = f u) ∧
        g m = raw k := by
    cases k with
    | zero =>
        change K.oneMeetLevel (f a) (pick (max M (f a))) = s ∧
          ∃ t : Nat, ∃ g : Nat → Nat,
            pick (max M (f a)) = F t ∧
            ReservedDiaryStage H K F (m + 1) g ∧
            (∀ u : Nat, u ∈ countableDiaryLeafPrefix H m →
              g u = f u) ∧
            g m = pick (max M (f a))
        exact (hPick (max M (f a))).2
    | succ k =>
        change K.oneMeetLevel (f a) (pick (raw k)) = s ∧
          ∃ t : Nat, ∃ g : Nat → Nat,
            pick (raw k) = F t ∧
            ReservedDiaryStage H K F (m + 1) g ∧
            (∀ u : Nat, u ∈ countableDiaryLeafPrefix H m →
              g u = f u) ∧
            g m = pick (raw k)
        exact (hPick (raw k)).2
  have hRawLeaf (k : Nat) : IsLeaf K (raw k) := by
    obtain ⟨_hMeet,t,_g,hEq,_Q,_hKeep,_hNew⟩ := hRawGood k
    rw [hEq]
    exact hFLeaf t
  obtain ⟨indices,hIndicesMono,hProperties,hPairs⟩ :=
    DK.exists_infinite_high_oneSplit_cone
      raw hRawMono.injective hRawLeaf B (max M (f a)) 0
  let values : Nat → Nat := fun k => raw (indices k)
  have hValuesMono : StrictMono values := by
    intro i j hij
    exact hRawMono (hIndicesMono hij)
  refine ⟨values,hValuesMono,?_,?_⟩
  · intro k
    have hLarge : max M (f a) < values k :=
      (hProperties k).2.1
    obtain ⟨hMeet,t,g,hEq,Q,hKeep,hNew⟩ :=
      hRawGood (indices k)
    exact ⟨lt_of_le_of_lt (le_max_left M (f a)) hLarge,
      hMeet,t,g,hEq,Q,hKeep,hNew⟩
  · intro i j hij
    obtain ⟨_hColour,hRole,hBound⟩ := hPairs i j hij
    exact ⟨hRole,hBound⟩

end DiaryLeafPriority
end ThreeUniformDiaries
