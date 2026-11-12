import ThreeUniformDiaries.DiaryGenericMixedConeIndivisibility
import ThreeUniformDiaries.DiarySingletonColourCofinalCone
import ThreeUniformDiaries.DiaryTwoLeafMarkerOrientation

/-!
# Track C: one cofinal simultaneous finite-root S1 profile contains generic subcopies

English proof and adversarial scope audit:
  janhubicka/3-uniform-diaries PR #298

In any full target RoleDiary, given a prescribed unordered induced
generic true-leaf range F[G] and ANY finite set W of fixed genuine
old target leaves (even outside F[G]), one finite vector of genuine
numerical S1 one-split meets with W contains induced generic
subcopies of F[G] beyond every target bound.

The profile is existential and fixed across all bounds; the generic
subcopies may vary. No exact source-prescribed profile, mixed
E2/E3/E5 between old and new, or persistent successor follows.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Finite complete table of NUMERIC S1 meets with a finite family
of roots. Every coordinate is bounded by the largest root index. -/
abbrev FiniteRootMeetProfile (W : Finset Nat) :=
  {w : Nat // w ∈ W} →
    Fin ((W.sup (fun x : Nat => x)) + 1)

/-- For any target bound B and finite set W of genuine target leaves,
there is an ACTUAL induced generic selfcopy of the original prescribed
unordered generic leaf range F[G] lying above B, and all its leaves
have one fixed vector of numeric S1 meets with EVERY root w∈W.

All profile entries are actual target one-splits strictly below the
corresponding root. The vector is chosen existentially, not prescribed
by an old source diary stage. -/
theorem RoleDiary.exists_generic_finiteRootMeet_subcopy_above
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (W : Finset Nat) (hRoots : ∀ w : Nat, w ∈ W → IsLeaf K w)
    (B : Nat) :
    ∃ p : FiniteRootMeetProfile W,
      (∀ w : {w : Nat // w ∈ W},
        IsOneSplit K (p w).val ∧ (p w).val < w.val) ∧
      ∃ (u : Ordered3Graph.Embedding G.graph G.graph),
        u.AuxTypeRespecting ∧
        ∀ t : Nat,
          B < F (u t) ∧
          (∀ w : {w : Nat // w ∈ W},
            K.oneMeetLevel w.val (F (u t)) = (p w).val) := by
  classical
  let T : Nat := W.sup (fun w : Nat => w)
  let C : Type := (FiniteRootMeetProfile W) × Bool
  letI : Nonempty C :=
    ⟨(fun _ => (⟨0, by omega⟩ : Fin (T + 1)), false)⟩
  let χ : Nat → C := fun n =>
    ((fun w : {w : Nat // w ∈ W} =>
      (⟨K.oneMeetLevel w.val (F n), by
        have hCap : K.oneMeetLevel w.val (F n) ≤ w.val :=
          (K.oneMeetLevel_le_min w.val (F n)).trans
            (min_le_left _ _)
        have hBound : w.val ≤ T :=
          Finset.le_sup (f := fun x : Nat => x) w.property
        omega⟩ : Fin (T + 1))),
      decide (max B T < F n))
  obtain ⟨u, hu, p, hMono⟩ :=
    generic_finite_vertex_colouring_monochromatic G χ
  have hInjective : Function.Injective (fun n : Nat => F (u n)) :=
    F.injective.comp u.strictMono.injective
  obtain ⟨N, hEventually⟩ :=
    injective_nat_eventually_above_bound
      (fun n : Nat => F (u n)) hInjective (max B T)
  have hAtN : decide (max B T < F (u N)) = p.2 := by
    have h := congrArg (fun z : C => z.2) (hMono N)
    change decide (max B T < F (u N)) = p.2 at h
    exact h
  have hpTrue : p.2 = true := by
    have hYes : decide (max B T < F (u N)) = true := by
      simp [hEventually N (le_refl N)]
    exact hAtN.symm.trans hYes
  have hHigh (t : Nat) : max B T < F (u t) := by
    have hAt : decide (max B T < F (u t)) = p.2 := by
      have h := congrArg (fun z : C => z.2) (hMono t)
      change decide (max B T < F (u t)) = p.2 at h
      exact h
    have hDec : decide (max B T < F (u t)) = true :=
      hAt.trans hpTrue
    by_cases hPositive : max B T < F (u t)
    · exact hPositive
    · simp [hPositive] at hDec
  let profile : FiniteRootMeetProfile W := p.1
  have hMeet (t : Nat) (w : {w : Nat // w ∈ W}) :
      K.oneMeetLevel w.val (F (u t)) = (profile w).val := by
    have h := congrArg (fun z : C => (z.1 w).val) (hMono t)
    change K.oneMeetLevel w.val (F (u t)) = (profile w).val at h
    exact h
  have hRole (w : {w : Nat // w ∈ W}) :
      IsOneSplit K (profile w).val ∧ (profile w).val < w.val := by
    have hSmall : w.val ≤ T :=
      Finset.le_sup (f := fun x : Nat => x) w.property
    have hwLt : w.val < F (u 0) :=
      lt_of_le_of_lt hSmall
        (lt_of_le_of_lt (le_max_right B T) (hHigh 0))
    have hNe : w.val ≠ F (u 0) := ne_of_lt hwLt
    have hwLeaf : IsLeaf K w.val := hRoots w.val w.property
    have hActualRole : IsOneSplit K
        (K.oneMeetLevel w.val (F (u 0))) :=
      DK.singleton_meets w.val (F (u 0))
        hwLeaf (hFLeaf (u 0)) hNe
    have hActualBelow : K.oneMeetLevel w.val (F (u 0)) < w.val :=
      DK.oneMeet_lt_left_of_distinct_leaves
        w.val (F (u 0)) hwLeaf (hFLeaf (u 0)) hNe
    rw [hMeet 0 w] at hActualRole hActualBelow
    exact ⟨hActualRole, hActualBelow⟩
  refine ⟨profile, hRole, u, hu, ?_⟩
  intro t
  exact ⟨lt_of_le_of_lt (le_max_left B T) (hHigh t),
    hMeet t⟩

/-- One SINGLE finite numerical S1 meet profile with EVERY genuine old
root w∈W supports induced generic subcopies in the original unordered
generic leaf range beyond ALL numerical target bounds B.

The profile is fixed before B. It is not source-prescribed, and
the subcopies at different B are not required to be coherent. -/
theorem RoleDiary.exists_uniform_finiteRootMeet_generic_subcopies
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (W : Finset Nat) (hRoots : ∀ w : Nat, w ∈ W → IsLeaf K w) :
    ∃ p : FiniteRootMeetProfile W,
      (∀ w : {w : Nat // w ∈ W},
        IsOneSplit K (p w).val ∧ (p w).val < w.val) ∧
      (∀ B : Nat,
        ∃ (u : Ordered3Graph.Embedding G.graph G.graph),
          u.AuxTypeRespecting ∧
          ∀ t : Nat,
            B < F (u t) ∧
            (∀ w : {w : Nat // w ∈ W},
              K.oneMeetLevel w.val (F (u t)) = (p w).val)) := by
  classical
  let R : FiniteRootMeetProfile W → Nat → Prop := fun p B =>
    ∃ (u : Ordered3Graph.Embedding G.graph G.graph),
      u.AuxTypeRespecting ∧
      ∀ t : Nat,
        B < F (u t) ∧
        (∀ w : {w : Nat // w ∈ W},
          K.oneMeetLevel w.val (F (u t)) = (p w).val)
  have hDown : ∀ p : FiniteRootMeetProfile W,
      ∀ B M : Nat, M ≤ B → R p B → R p M := by
    intro p B M hMB
    rintro ⟨u, hu, hAll⟩
    refine ⟨u, hu, ?_⟩
    intro t
    obtain ⟨hLarge, hMeets⟩ := hAll t
    exact ⟨lt_of_le_of_lt hMB hLarge, hMeets⟩
  have hCover : ∀ B : Nat,
      ∃ p : FiniteRootMeetProfile W,
        p ∈ (Finset.univ : Finset (FiniteRootMeetProfile W)) ∧
        R p B := by
    intro B
    obtain ⟨p, _hRoles, u, hu, hAll⟩ :=
      DK.exists_generic_finiteRootMeet_subcopy_above
        G F hFLeaf W hRoots B
    exact ⟨p, Finset.mem_univ _, u, hu, hAll⟩
  obtain ⟨p, _hp, hRecur⟩ :=
    finite_choice_persistent_of_downward_type
      (Finset.univ : Finset (FiniteRootMeetProfile W))
      R hDown hCover
  have hRoles (w : {w : Nat // w ∈ W}) :
      IsOneSplit K (p w).val ∧ (p w).val < w.val := by
    obtain ⟨u, _hu, hAll⟩ := hRecur w.val
    have hwLt : w.val < F (u 0) := (hAll 0).1
    have hNe : w.val ≠ F (u 0) := ne_of_lt hwLt
    have hwLeaf : IsLeaf K w.val := hRoots w.val w.property
    have hMeet : K.oneMeetLevel w.val (F (u 0)) = (p w).val :=
      (hAll 0).2 w
    have hActualRole : IsOneSplit K
        (K.oneMeetLevel w.val (F (u 0))) :=
      DK.singleton_meets w.val (F (u 0))
        hwLeaf (hFLeaf (u 0)) hNe
    have hActualBelow : K.oneMeetLevel w.val (F (u 0)) < w.val :=
      DK.oneMeet_lt_left_of_distinct_leaves
        w.val (F (u 0)) hwLeaf (hFLeaf (u 0)) hNe
    rw [hMeet] at hActualRole hActualBelow
    exact ⟨hActualRole, hActualBelow⟩
  exact ⟨p, hRoles, hRecur⟩

end DiaryLeafPriority
end ThreeUniformDiaries
