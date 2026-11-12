import ThreeUniformDiaries.DiaryCofinalGenericFiniteColourSubcopies
import ThreeUniformDiaries.DiaryCofinalGenericE5S1E2S2E3Profile
import ThreeUniformDiaries.DiaryFiniteSingletonColour

/-!
# Track C: complete finite mixed-colour and S1/S2 profiles on GENERIC subcopies

English proof and adversarial audit:
  janhubicka/3-uniform-diaries PR #306

In the original unordered induced generic true-leaf range F[G] of a
full target RoleDiary, fix an arbitrary finite set W of genuine old
target leaf roots (also allowed outside F[G]), and a finite target
mixed singleton colour cut C.

The complete C-colour, every exact numeric S1 meet with W, and every
cross-S2 full pair meet (old ordered pair from W versus (w,new leaf))
form ONE FINITE product palette. The verified generic finite-colour
subcopy theorem gives ONE profile triple (c,p,q) such that, beyond
EVERY target numerical bound, an ENTIRE induced generic selfcopy has
this SAME triple at ALL of its genuine target leaves.

All p entries are true one-splits below the corresponding root.
All q entries satisfy the full RoleDiary S2 trichotomy: cap, marker
one, or genuine two-split. E2/E3 incidence polarity at true splits
then follows from the already verified V1/V2 witness laws.

The full-colour cut and W are fixed, but the numerical p and q and
mixed finite colour c are selected EXISTENTIALLY: they need NOT be the
specific source-required split table of an old diary stage. Nothing
here constructs an actual reserved successor or countable
unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- One complete finite mixed singleton colour, all exact numerical
old-root S1 meets, and every cross-S2 pair meet are simultaneously
constant on an INDUCED GENERIC SUBCOPY in every arbitrarily late
target tail. The winning triple is fixed before the tail cutoff M.

The original F is an unordered induced embedding and may rearrange
target order. The roots W need not lie in F[G]. All target images
remain actual genuine leaves and their full induced E5 reduct is
preserved inside each selected generic subcopy.

The S1/S2 roles are genuine target roles, but the selected values
are not the source-prescribed generator-table values. -/
theorem RoleDiary.exists_uniform_generic_fullColour_S1_S2_subcopies
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (W : Finset Nat) (hRoots : ∀ w : Nat, w ∈ W → IsLeaf K w)
    (Cut : Nat) :
    ∃ c : Fin Cut → Fin Cut → Bool,
      ∃ p : FiniteRootMeetProfile W,
        ∃ q : FiniteRootCrossPairMeetProfile W,
          (∀ w : {w : Nat // w ∈ W},
            IsOneSplit K (p w).val ∧ (p w).val < w.val) ∧
          (∀ ab : {ab : Nat × Nat // ab ∈ finiteOrderedLeafPairs W},
            ∀ w : {w : Nat // w ∈ W},
              (q ab w).val = min ab.val.1 w.val ∨
              (q ab w).val = 1 ∨ IsTwoSplit K (q ab w).val) ∧
          (∀ M : Nat,
            ∃ (u : Ordered3Graph.Embedding G.graph G.graph),
              u.AuxTypeRespecting ∧
              ∀ t : Nat,
                M < F (u t) ∧ IsLeaf K (F (u t)) ∧
                DiaryLowerBoundColors.singletonColour K Cut (F (u t)) = c ∧
                (∀ w : {w : Nat // w ∈ W},
                  K.oneMeetLevel w.val (F (u t)) = (p w).val) ∧
                (∀ ab : {ab : Nat × Nat //
                    ab ∈ finiteOrderedLeafPairs W},
                  ∀ w : {w : Nat // w ∈ W},
                    K.twoMeetLevel ab.val.1 ab.val.2
                      w.val (F (u t)) = (q ab w).val)) := by
  classical
  let T : Nat := W.sup (fun w : Nat => w)
  let C : Type :=
    (Fin Cut → Fin Cut → Bool) ×
      (FiniteRootMeetProfile W × FiniteRootCrossPairMeetProfile W)
  letI : Nonempty C :=
    ⟨(fun _ _ => false,
      (fun _ => (⟨0, by omega⟩ : Fin (T + 1)),
       fun _ _ => (⟨0, by omega⟩ : Fin (T + 1))))⟩
  let rho : Nat → C := fun n =>
    (DiaryLowerBoundColors.singletonColour K Cut (F n),
      (fun w : {w : Nat // w ∈ W} =>
        (⟨K.oneMeetLevel w.val (F n), by
          have hCap : K.oneMeetLevel w.val (F n) ≤ w.val :=
            (K.oneMeetLevel_le_min w.val (F n)).trans
              (min_le_left _ _)
          have hw : w.val ≤ T :=
            Finset.le_sup (f := fun x : Nat => x) w.property
          omega⟩ : Fin (T + 1)),
       fun ab : {ab : Nat × Nat // ab ∈ finiteOrderedLeafPairs W} =>
         fun w : {w : Nat // w ∈ W} =>
           (⟨K.twoMeetLevel ab.val.1 ab.val.2 w.val (F n), by
             have hCap : K.twoMeetLevel ab.val.1 ab.val.2
                 w.val (F n) ≤ w.val :=
               (K.twoMeetLevel_le_min
                 ab.val.1 ab.val.2 w.val (F n)).trans
                 (min_le_right _ _)
             have hw : w.val ≤ T :=
               Finset.le_sup (f := fun x : Nat => x) w.property
             omega⟩ : Fin (T + 1))))
  obtain ⟨r, hAll⟩ :=
    exists_uniform_cofinal_generic_monochromatic_subcopies
      G rho F F.injective
  let c := r.1
  let p := r.2.1
  let q := r.2.2
  have hOneRole (w : {w : Nat // w ∈ W}) :
      IsOneSplit K (p w).val ∧ (p w).val < w.val := by
    obtain ⟨u, _hu, hu⟩ := hAll T
    have hHigh : T < F (u 0) := (hu 0).1
    have hRootBound : w.val ≤ T :=
      Finset.le_sup (f := fun x : Nat => x) w.property
    have hBefore : w.val < F (u 0) :=
      lt_of_le_of_lt hRootBound hHigh
    have hRootLeaf : IsLeaf K w.val := hRoots w.val w.property
    have hActualLeaf : IsLeaf K (F (u 0)) := hFLeaf (u 0)
    have hMeet : K.oneMeetLevel w.val (F (u 0)) = (p w).val := by
      have h := congrArg (fun z : C => (z.2.1 w).val) (hu 0).2
      change K.oneMeetLevel w.val (F (u 0)) = (p w).val at h
      exact h
    have hRole : IsOneSplit K
        (K.oneMeetLevel w.val (F (u 0))) :=
      DK.singleton_meets w.val (F (u 0))
        hRootLeaf hActualLeaf (ne_of_lt hBefore)
    have hBelow : K.oneMeetLevel w.val (F (u 0)) < w.val :=
      DK.oneMeet_lt_left_of_distinct_leaves
        w.val (F (u 0)) hRootLeaf hActualLeaf
        (ne_of_lt hBefore)
    rw [hMeet] at hRole hBelow
    exact ⟨hRole, hBelow⟩
  have hTwoRole
      (ab : {ab : Nat × Nat // ab ∈ finiteOrderedLeafPairs W})
      (w : {w : Nat // w ∈ W}) :
      (q ab w).val = min ab.val.1 w.val ∨
      (q ab w).val = 1 ∨ IsTwoSplit K (q ab w).val := by
    obtain ⟨u, _hu, hu⟩ := hAll T
    have hHigh : T < F (u 0) := (hu 0).1
    have hRootBound : w.val ≤ T :=
      Finset.le_sup (f := fun x : Nat => x) w.property
    have hBefore : w.val < F (u 0) :=
      lt_of_le_of_lt hRootBound hHigh
    have hOldPair : ab.val.1 < ab.val.2 :=
      (Finset.mem_filter.mp ab.property).2
    have hPairMem :
        (ab.val.1, ab.val.2) ∈ W.product W :=
      (Finset.mem_filter.mp ab.property).1
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hPairMem
    have hA : IsLeaf K ab.val.1 := hRoots ab.val.1 ha
    have hB : IsLeaf K ab.val.2 := hRoots ab.val.2 hb
    have hW : IsLeaf K w.val := hRoots w.val w.property
    have hV : IsLeaf K (F (u 0)) := hFLeaf (u 0)
    have hMeet :
        K.twoMeetLevel ab.val.1 ab.val.2 w.val (F (u 0)) =
          (q ab w).val := by
      have h := congrArg (fun z : C => (z.2.2 ab w).val) (hu 0).2
      change K.twoMeetLevel ab.val.1 ab.val.2
        w.val (F (u 0)) = (q ab w).val at h
      exact h
    have hCases := DK.pair_meets ab.val.1 ab.val.2
      w.val (F (u 0)) hOldPair hBefore hA hB hW hV
    rw [hMeet] at hCases
    exact hCases
  refine ⟨c, p, q, hOneRole, hTwoRole, ?_⟩
  intro M
  obtain ⟨u, hu, hEvery⟩ := hAll M
  refine ⟨u, hu, ?_⟩
  intro t
  obtain ⟨hHigh, hProfile⟩ := hEvery t
  have hCol : DiaryLowerBoundColors.singletonColour K Cut (F (u t)) = c := by
    have h := congrArg (fun z : C => z.1) hProfile
    change DiaryLowerBoundColors.singletonColour K Cut (F (u t)) = c at h
    exact h
  have hOne (w : {w : Nat // w ∈ W}) :
      K.oneMeetLevel w.val (F (u t)) = (p w).val := by
    have h := congrArg (fun z : C => (z.2.1 w).val) hProfile
    change K.oneMeetLevel w.val (F (u t)) = (p w).val at h
    exact h
  have hTwo (ab : {ab : Nat × Nat // ab ∈ finiteOrderedLeafPairs W})
      (w : {w : Nat // w ∈ W}) :
      K.twoMeetLevel ab.val.1 ab.val.2 w.val (F (u t)) =
        (q ab w).val := by
    have h := congrArg (fun z : C => (z.2.2 ab w).val) hProfile
    change K.twoMeetLevel ab.val.1 ab.val.2 w.val (F (u t)) =
      (q ab w).val at h
    exact h
  exact ⟨hHigh, hFLeaf (u t), hCol, hOne, hTwo⟩

end DiaryLeafPriority
end ThreeUniformDiaries
