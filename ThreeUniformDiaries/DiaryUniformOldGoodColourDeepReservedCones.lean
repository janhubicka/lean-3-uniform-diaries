import ThreeUniformDiaries.DiaryChosenOldSupportSaturatedGoodColour
import ThreeUniformDiaries.DiaryInfiniteHighOneSplitCone

/-!
# Track D: one fixed complete old support and one good colour
# have arbitrarily deep genuine reserved next-leaf S1 cones

The checked generic finite-old-set avoidance / padded finite diary
unavoidability result chooses ONE complete old reserved S_m map f
whose genuine compatible immediate next-leaf images occur cofinally.
The checked old-cut tail replacement and finite palette recurrence
choose ONE complete singleton colour c, at the fixed old-stage cut,
that occurs cofinally and is eventually wholly compatible with f.

Crucially both f and c are chosen BEFORE any additional target
S1 meet depth B or numerical size cutoff M. Inside the actual
cofinal c-coloured valid successor set, recursively choose a strictly
increasing numerical sequence of valid target new-leaf images.
Now apply the existing high S1-cone theorem INSIDE that sequence.
Every selected image remains in the original F-range, still has
colour c and a real complete reserved successor over the same f,
and any two selected leaves meet at a genuine S1 split above B.

Thus ONE literally fixed full old diary support and ONE full
old-cut good colour give deep actual immediate-successor cones
at EVERY requested depth B.

The choice of a high-S1 subcone may depend on B and M, and
may not produce an induced generic leaf E5 copy or a single
new image surviving all longer finite source horizons.
No unconditional countable diary unavoidability is asserted.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- For EVERY new source leaf m with at least one old selected leaf
and every original unordered induced generic target leaf range,
there exist a SINGLE whole genuine old reserved support f and a
SINGLE cofinally inhabited, eventually SATURATED complete old-cut
mixed colour c such that for ALL depths B and target bounds M:

* a strictly TARGET-numerically increasing sequence v_k>M of
  TRUE target leaves in the ORIGINAL prescribed F-range exists;
* each v_k has colour c and an actual complete reserved immediate
  new-leaf stage g_k fixing the entire old support f;
* every two distinct v_i,v_j have a genuine singleton split meet
  numerically at least B.

The chosen f and c do NOT depend on B,M. No assertion is made that
one of the v_k survives even one later finite continuation horizon. -/
theorem RoleDiary.exists_uniform_old_support_good_colour_deep_reserved_cones
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (m : Nat) (hm : IsLeaf H m)
    (hOldNonempty : (countableDiaryLeafPrefix H m).Nonempty) :
    ∃ f : Nat → Nat,
      ReservedDiaryStage H K (fun t : Nat => F t) m f ∧
      ∃ c : Fin (oldStageTailCut H m f) →
          Fin (oldStageTailCut H m f) → Bool,
        (∃ T : Nat, ∀ t : Nat, T ≤ F t →
          DiaryLowerBoundColors.singletonColour K
            (oldStageTailCut H m f) (F t) = c →
          HasCompatibleReservedNextLeaf H K
            (fun t : Nat => F t) f m (F t)) ∧
        (∀ B M : Nat,
          ∃ values : Nat → Nat,
            StrictMono values ∧
            (∀ k : Nat,
              M < values k ∧
              DiaryLowerBoundColors.singletonColour K
                (oldStageTailCut H m f) (values k) = c ∧
              ∃ t : Nat, ∃ g : Nat → Nat,
                values k = F t ∧
                ReservedDiaryStage H K
                  (fun t : Nat => F t) (m + 1) g ∧
                CofinalDiaryStageCompatible H m f g ∧
                g m = values k) ∧
            (∀ i j : Nat, i < j →
              IsOneSplit K (K.oneMeetLevel (values i) (values j)) ∧
              B ≤ K.oneMeetLevel (values i) (values j))) := by
  classical
  obtain ⟨f,Pf,c,hRecur,hSat⟩ :=
    DH.exists_chosen_old_support_with_saturated_good_colour
      DK G F hFLeaf m hm hOldNonempty
  refine ⟨f,Pf,c,hSat,?_⟩
  intro B M
  let C := oldStageTailCut H m f
  have hValid (X : Nat) :
      ∃ v : Nat,
        X < v ∧ IsLeaf K v ∧
        DiaryLowerBoundColors.singletonColour K C v = c ∧
        ∃ t : Nat, ∃ g : Nat → Nat,
          v = F t ∧
          ReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g ∧
          CofinalDiaryStageCompatible H m f g ∧
          g m = v := by
    obtain ⟨t,hHigh,hColour,hGood⟩ := hRecur X
    obtain ⟨g,Q,hOld,hNew⟩ := hGood
    exact ⟨F t,hHigh,hFLeaf t,hColour,t,g,rfl,Q,hOld,hNew⟩
  let pick : Nat → Nat := fun X => Classical.choose (hValid X)
  have hPick (X : Nat) :
      X < pick X ∧ IsLeaf K (pick X) ∧
      DiaryLowerBoundColors.singletonColour K C (pick X) = c ∧
      ∃ t : Nat, ∃ g : Nat → Nat,
        pick X = F t ∧
        ReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g ∧
        CofinalDiaryStageCompatible H m f g ∧
        g m = pick X := by
    exact Classical.choose_spec (hValid X)
  let raw : Nat → Nat :=
    Nat.rec (pick (max B M)) (fun _ prev => pick prev)
  have hRawStep (k : Nat) : raw k < raw (k+1) := by
    change raw k < pick (raw k)
    exact (hPick (raw k)).1
  have hRawMono : StrictMono raw :=
    strictMono_nat_of_lt_succ hRawStep
  have hRawGood (k : Nat) :
      IsLeaf K (raw k) ∧
      DiaryLowerBoundColors.singletonColour K C (raw k) = c ∧
      ∃ t : Nat, ∃ g : Nat → Nat,
        raw k = F t ∧
        ReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g ∧
        CofinalDiaryStageCompatible H m f g ∧
        g m = raw k := by
    cases k with
    | zero =>
        change IsLeaf K (pick (max B M)) ∧
          DiaryLowerBoundColors.singletonColour K C (pick (max B M)) = c ∧
          ∃ t : Nat, ∃ g : Nat → Nat,
            pick (max B M) = F t ∧
            ReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g ∧
            CofinalDiaryStageCompatible H m f g ∧
            g m = pick (max B M)
        exact (hPick (max B M)).2
    | succ k =>
        change IsLeaf K (pick (raw k)) ∧
          DiaryLowerBoundColors.singletonColour K C (pick (raw k)) = c ∧
          ∃ t : Nat, ∃ g : Nat → Nat,
            pick (raw k) = F t ∧
            ReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g ∧
            CofinalDiaryStageCompatible H m f g ∧
            g m = pick (raw k)
        exact (hPick (raw k)).2
  have hRawLeaf (k : Nat) : IsLeaf K (raw k) :=
    (hRawGood k).1
  obtain ⟨indices,hIndexMono,hProperties,hPairs⟩ :=
    DK.exists_infinite_high_oneSplit_cone
      raw hRawMono.injective hRawLeaf B M 0
  let values : Nat → Nat := fun k => raw (indices k)
  have hValuesMono : StrictMono values := by
    intro i j hij
    exact hRawMono (hIndexMono hij)
  refine ⟨values,hValuesMono,?_,?_⟩
  · intro k
    have hBig : M < values k := (hProperties k).2.1
    obtain ⟨_hLeaf,hColour,t,g,hEq,Q,hOld,hNew⟩ :=
      hRawGood (indices k)
    exact ⟨hBig,hColour,t,g,hEq,Q,hOld,hNew⟩
  · intro i j hij
    obtain ⟨_hBColour,hRole,hBound⟩ := hPairs i j hij
    exact ⟨hRole,hBound⟩

end DiaryLeafPriority
end ThreeUniformDiaries
