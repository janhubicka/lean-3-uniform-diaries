import ThreeUniformDiaries.DiaryFirstLeafUniformAllHorizonColour
import ThreeUniformDiaries.DiaryFiniteGoodOldCutCandidateColours
import ThreeUniformDiaries.DiaryInfiniteHighOneSplitCone
import ThreeUniformDiaries.DiaryFiniteCandidateOldColourDichotomy

/-!
# Track C: ONE first-leaf good colour supports deep S1 cones at EVERY finite horizon

English-first proof and adversarial scope audit:
  janhubicka/3-uniform-diaries PR #362.

For a genuine FIRST source leaf m with EMPTY old selected-leaf
prefix, the kernel-checked all-horizon result provides ONE
finitely persistent complete old marker support f and ONE
complete mixed oldStageTailCut singleton colour c with real
cofinally high reserved continuation stages at EVERY finite
source horizon m+1+n, retaining f and c simultaneously.

The colour c belongs to the exact Track C finite good-candidate
palette. Every high true F-range leaf of c is a complete bare
finite candidate, and all sufficiently high ones are actual
compatible IMMEDIATE reserved successors.

For each horizon n, depth D, and target height M, choose an
increasing sequence of ACTUAL compatible reserved n-horizon
witnesses of colour c and apply the independently checked
infinite-high-S1-cone lemma INSIDE that sequence. ONE f and ONE
c are selected before ALL n,D,M, not separately for each horizon.

Crucial negative scope: no one new leaf value is required to
survive all horizons; witness stages may change with n,D,M.
The selected high-S1 cone need not be an induced generic
3-hypergraph copy or realize any bipolar E5 pair. This is NOT
countable diary unavoidability or a big Ramsey degree result.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- For the first genuine source leaf, ONE complete genuinely
finitely persistent old marker support f and ONE exact finite
good old-cut singleton colour c work for EVERY finite source
horizon, arbitrarily deep pairwise genuine S1 one-split meets,
and arbitrarily high target numerical cutoff.

Each selected leaf has its own actual RESERVED full continuation
stage m+1+n, compatible with that SAME old supported f. No
single new image is persistent through the unbounded horizons. -/
theorem RoleDiary.exists_first_leaf_uniform_all_horizon_good_colour_deep_cones
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (m : Nat) (hm : IsLeaf H m)
    (hFirst : countableDiaryLeafPrefix H m = ∅) :
    ∃ f : Nat → Nat,
      PersistentReservedDiaryStage H K
        (fun t : Nat => F t) m f ∧
      ∃ c : Fin (oldStageTailCut H m f) →
          Fin (oldStageTailCut H m f) → Bool,
        c ∈ goodOldCutCandidateColours H K
          (fun t : Nat => F t) f m ∧
        (∀ w : Nat,
          oldStageTailCut H m f ≤ w →
          IsLeaf K w →
          (∃ t : Nat, w = F t) →
          DiaryLowerBoundColors.singletonColour K
            (oldStageTailCut H m f) w = c →
          FiniteNewLeafCandidateCondition H K
            (fun t : Nat => F t) m f w) ∧
        (∃ T : Nat, ∀ t : Nat, T ≤ F t →
          DiaryLowerBoundColors.singletonColour K
            (oldStageTailCut H m f) (F t) = c →
          HasCompatibleReservedNextLeaf H K
            (fun t : Nat => F t) f m (F t)) ∧
        (∀ n D M : Nat,
          ∃ values : Nat → Nat,
            StrictMono values ∧
            (∀ k : Nat,
              M < values k ∧
              DiaryLowerBoundColors.singletonColour K
                (oldStageTailCut H m f) (values k) = c ∧
              ∃ t : Nat, ∃ g : Nat → Nat,
                values k = F t ∧
                ReservedDiaryStage H K
                  (fun t : Nat => F t) (m + 1 + n) g ∧
                CofinalDiaryStageCompatible H m f g ∧
                g m = values k) ∧
            (∀ i j : Nat, i < j →
              IsOneSplit K
                (K.oneMeetLevel (values i) (values j)) ∧
              D ≤ K.oneMeetLevel (values i) (values j))) := by
  classical
  obtain ⟨f, Pf, c, hAll, hSat⟩ :=
    DH.exists_first_leaf_uniform_all_horizon_old_support_and_colour
      DK G F hFLeaf m hm hFirst
  have hPalette :
      c ∈ goodOldCutCandidateColours H K
        (fun t : Nat => F t) f m := by
    obtain ⟨t₀,g₀,hHigh₀,Q₀,hOld₀,hNew₀,hColour₀⟩ :=
      hAll 0 (oldStageTailCut H m f)
    have QImmediate :
        ReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g₀ :=
      Q₀.restrict (by omega)
    have hGood :
        HasCompatibleReservedNextLeaf H K
          (fun t : Nat => F t) f m (F t₀) :=
      ⟨g₀,QImmediate,hOld₀,hNew₀⟩
    have hFinite :
        FiniteNewLeafCandidateCondition H K
          (fun t : Nat => F t) m f (F t₀) :=
      ((Pf.1.finite_candidate_iff_compatible_next_leaf DH hm).mpr
        hGood).1
    simp only [goodOldCutCandidateColours, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨F t₀, Nat.le_of_lt hHigh₀, hFLeaf t₀,
      ⟨t₀,rfl⟩, hFinite, hColour₀⟩
  refine ⟨f,Pf,c,hPalette,?_,hSat,?_⟩
  · intro w hw hwLeaf hwRange hwColour
    have hMember :
        DiaryLowerBoundColors.singletonColour K
          (oldStageTailCut H m f) w ∈
          goodOldCutCandidateColours H K
            (fun t : Nat => F t) f m := by
      rw [hwColour]
      exact hPalette
    exact (Pf.1.1.full_candidate_iff_good_oldCut_colour
      hm hw hwLeaf hwRange).mpr hMember
  · intro n D M
    let Cut := oldStageTailCut H m f
    have hValid (X : Nat) :
        ∃ v : Nat,
          X < v ∧ IsLeaf K v ∧
          DiaryLowerBoundColors.singletonColour K Cut v = c ∧
          ∃ t : Nat, ∃ g : Nat → Nat,
            v = F t ∧
            ReservedDiaryStage H K
              (fun t : Nat => F t) (m + 1 + n) g ∧
            CofinalDiaryStageCompatible H m f g ∧
            g m = v := by
      obtain ⟨t,g,hHigh,Q,hOld,hNew,hColour⟩ := hAll n X
      exact ⟨F t,hHigh,hFLeaf t,hColour,t,g,rfl,Q,hOld,hNew⟩
    let pick : Nat → Nat := fun X => Classical.choose (hValid X)
    have hPick (X : Nat) :
        X < pick X ∧ IsLeaf K (pick X) ∧
        DiaryLowerBoundColors.singletonColour K Cut (pick X) = c ∧
        ∃ t : Nat, ∃ g : Nat → Nat,
          pick X = F t ∧
          ReservedDiaryStage H K
            (fun t : Nat => F t) (m + 1 + n) g ∧
          CofinalDiaryStageCompatible H m f g ∧
          g m = pick X :=
      Classical.choose_spec (hValid X)
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
          ReservedDiaryStage H K
            (fun t : Nat => F t) (m + 1 + n) g ∧
          CofinalDiaryStageCompatible H m f g ∧
          g m = raw k := by
      cases k with
      | zero =>
          change IsLeaf K (pick (max D M)) ∧
            DiaryLowerBoundColors.singletonColour K Cut
              (pick (max D M)) = c ∧
            ∃ t : Nat, ∃ g : Nat → Nat,
              pick (max D M) = F t ∧
              ReservedDiaryStage H K
                (fun t : Nat => F t) (m + 1 + n) g ∧
              CofinalDiaryStageCompatible H m f g ∧
              g m = pick (max D M)
          exact (hPick (max D M)).2
      | succ k =>
          change IsLeaf K (pick (raw k)) ∧
            DiaryLowerBoundColors.singletonColour K Cut
              (pick (raw k)) = c ∧
            ∃ t : Nat, ∃ g : Nat → Nat,
              pick (raw k) = F t ∧
              ReservedDiaryStage H K
                (fun t : Nat => F t) (m + 1 + n) g ∧
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
      obtain ⟨_hColour,hRole,hBound⟩ := hPairs i j hij
      exact ⟨hRole,hBound⟩

end DiaryLeafPriority
end ThreeUniformDiaries
