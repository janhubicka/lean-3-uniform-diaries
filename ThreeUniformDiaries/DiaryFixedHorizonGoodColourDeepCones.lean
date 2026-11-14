import ThreeUniformDiaries.DiaryFixedHorizonCofinalGoodOldColour
import ThreeUniformDiaries.DiaryInfiniteHighOneSplitCone

/-!
# Track C: arbitrarily deep S1 cones of ACTUAL q-horizon reserved witnesses

English-first mathematical proof and adversarial quantifier audit:
  janhubicka/3-uniform-diaries PR #345.

For a specified finite future horizon q >= m+1, the checked Track C
fixed-horizon theorem chooses one complete literal old reserved
support f and one complete oldStageTailCut mixed singleton colour c
with cofinally many REAL q-stage reserved witnesses g extending f,
whose new leaf m maps to a true F-range target leaf of colour c.

Fix f,c BEFORE the requested S1 depth D and target lower bound M.
Recursively choose a strictly target-value-increasing sequence of
ACTUAL q-horizon witnesses in that SAME colour. The validated
infinite high S1 cone theorem, applied INSIDE this sequence, gives
an infinite subsequence of genuine high one-split meets; every
selected image retains its original q-horizon reserved witness,
complete old-support compatibility, and full old-cut colour c.

The selected f,c MAY DEPEND ON THE FINITE q, and the subsequence
may depend on D,M. No induced generic hypergraph copy in this
cone, no one fixed next image through all future horizons, no
countable diary unavoidability or exact BRD theorem is claimed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- For one prescribed future finite source horizon q, there exist
ONE fixed complete genuine old support f and ONE full mixed
old-cut good colour c such that for EVERY target S1 depth D
and target cutoff M an infinite numerically increasing sequence
of ACTUAL q-stage reserved new-leaf images of colour c exists.

All q-stage maps in the selected sequence preserve the SAME f on
all old S_m support. Their pairwise S1 meets are genuine one-splits
at level >= D. No generic induced copy or all-horizon persistence
is asserted; f,c may depend on q. -/
theorem RoleDiary.exists_fixed_horizon_good_colour_deep_q_cones
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (m q : Nat) (hmq : m + 1 ≤ q)
    (hm : IsLeaf H m)
    (hOldNonempty : (countableDiaryLeafPrefix H m).Nonempty) :
    ∃ f : Nat → Nat,
      ReservedDiaryStage H K (fun t : Nat => F t) m f ∧
      ∃ c : Fin (oldStageTailCut H m f) →
          Fin (oldStageTailCut H m f) → Bool,
        c ∈ goodOldCutCandidateColours H K
          (fun t : Nat => F t) f m ∧
        (∃ T : Nat, ∀ t : Nat, T ≤ F t →
          DiaryLowerBoundColors.singletonColour K
            (oldStageTailCut H m f) (F t) = c →
          HasCompatibleReservedNextLeaf H K
            (fun t : Nat => F t) f m (F t)) ∧
        (∀ D M : Nat,
          ∃ values : Nat → Nat,
            StrictMono values ∧
            (∀ k : Nat,
              M < values k ∧
              DiaryLowerBoundColors.singletonColour K
                (oldStageTailCut H m f) (values k) = c ∧
              ∃ t : Nat, ∃ g : Nat → Nat,
                values k = F t ∧
                ReservedDiaryStage H K
                  (fun t : Nat => F t) q g ∧
                CofinalDiaryStageCompatible H m f g ∧
                g m = values k) ∧
            (∀ i j : Nat, i < j →
              IsOneSplit K (K.oneMeetLevel (values i) (values j)) ∧
              D ≤ K.oneMeetLevel (values i) (values j))) := by
  classical
  obtain ⟨f,Pf,c,hRecur,hPalette,_hFinite,hSat⟩ :=
    DH.exists_fixed_horizon_cofinal_good_oldCut_colour
      DK G F hFLeaf m q hmq hm hOldNonempty
  refine ⟨f,Pf,c,hPalette,hSat,?_⟩
  intro D M
  let Cut := oldStageTailCut H m f
  have hValid (X : Nat) :
      ∃ v : Nat,
        X < v ∧ IsLeaf K v ∧
        DiaryLowerBoundColors.singletonColour K Cut v = c ∧
        ∃ t : Nat, ∃ g : Nat → Nat,
          v = F t ∧
          ReservedDiaryStage H K (fun t : Nat => F t) q g ∧
          CofinalDiaryStageCompatible H m f g ∧
          g m = v := by
    obtain ⟨t,g,hHigh,Q,hOld,hNew,hColour⟩ := hRecur X
    exact ⟨F t,hHigh,hFLeaf t,hColour,t,g,rfl,Q,hOld,hNew⟩
  let pick : Nat → Nat := fun X => Classical.choose (hValid X)
  have hPick (X : Nat) :
      X < pick X ∧ IsLeaf K (pick X) ∧
      DiaryLowerBoundColors.singletonColour K Cut (pick X) = c ∧
      ∃ t : Nat, ∃ g : Nat → Nat,
        pick X = F t ∧
        ReservedDiaryStage H K (fun t : Nat => F t) q g ∧
        CofinalDiaryStageCompatible H m f g ∧
        g m = pick X := by
    exact Classical.choose_spec (hValid X)
  let raw : Nat → Nat :=
    Nat.rec (pick (max D M)) (fun _ prev => pick prev)
  have hRawStep (k : Nat) : raw k < raw (k + 1) := by
    change raw k < pick (raw k)
    exact (hPick (raw k)).1
  have hRawMono : StrictMono raw :=
    strictMono_nat_of_lt_succ hRawStep
  have hRawGood (k : Nat) :
      IsLeaf K (raw k) ∧
      DiaryLowerBoundColors.singletonColour K Cut (raw k) = c ∧
      ∃ t : Nat, ∃ g : Nat → Nat,
        raw k = F t ∧
        ReservedDiaryStage H K (fun t : Nat => F t) q g ∧
        CofinalDiaryStageCompatible H m f g ∧
        g m = raw k := by
    cases k with
    | zero =>
        change IsLeaf K (pick (max D M)) ∧
          DiaryLowerBoundColors.singletonColour K Cut (pick (max D M)) = c ∧
          ∃ t : Nat, ∃ g : Nat → Nat,
            pick (max D M) = F t ∧
            ReservedDiaryStage H K (fun t : Nat => F t) q g ∧
            CofinalDiaryStageCompatible H m f g ∧
            g m = pick (max D M)
        exact (hPick (max D M)).2
    | succ k =>
        change IsLeaf K (pick (raw k)) ∧
          DiaryLowerBoundColors.singletonColour K Cut (pick (raw k)) = c ∧
          ∃ t : Nat, ∃ g : Nat → Nat,
            pick (raw k) = F t ∧
            ReservedDiaryStage H K (fun t : Nat => F t) q g ∧
            CofinalDiaryStageCompatible H m f g ∧
            g m = pick (raw k)
        exact (hPick (raw k)).2
  have hRawLeaf (k : Nat) : IsLeaf K (raw k) :=
    (hRawGood k).1
  obtain ⟨indices,hIndexMono,hProperties,hPairs⟩ :=
    DK.exists_infinite_high_oneSplit_cone
      raw hRawMono.injective hRawLeaf D M 0
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
    obtain ⟨_hDColour,hRole,hBound⟩ := hPairs i j hij
    exact ⟨hRole,hBound⟩

end DiaryLeafPriority
end ThreeUniformDiaries
