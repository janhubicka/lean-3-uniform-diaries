import ThreeUniformDiaries.DiaryGenericFiniteTupleForwardAvoidance
import ThreeUniformDiaries.DiaryIndependentReservedStageExistence
import ThreeUniformDiaries.DiaryReservedFiniteHorizonCompatibility
import ThreeUniformDiaries.DiaryLeafGeneratedStageCompatibility
import ThreeUniformDiaries.DiaryUpperBoundDirectTransfer

/-!
# Track D: some COMPLETE old finite diary support has unbounded genuine next leaves

The generic finite-old-set avoidance theorem (from the verified binary
forward-avoidance lemma) gives a stronger contradiction than its
two-leaf instance. The actual finite-source unavoidability and
complete-prefix padding produce a genuine reserved source stage in
EVERY induced generic subcopy of the target leaves.

If no single full old-support map had arbitrarily late next leaves,
then every fixed finite set A of old leaf image indices would have an
eventual target bound beyond which NO genuine reserved next-leaf stage
could use old images all in F[A]. Indeed, there are only finitely many
assignments of old leaves into F[A], and one assignment recurring
cofinally would force the ENTIRE old support to agree, since all old
S1/S2 nonleaf generator images are functions of the old leaf images.

The generic finite-old-set avoidance theorem then supplies an induced
generic subcopy whose new vertices avoid every such stage with a
nonempty set of previously chosen old leaves. But the padded finite
unavoidability theorem still supplies a genuine reserved source stage
inside that very subcopy, giving a contradiction.

Thus at EVERY source new-leaf stage with at least one old leaf there
exists SOME complete, literally fixed old support map admitting
arbitrarily high actual reserved immediate next-leaf realizations
inside the ORIGINAL unordered generic leaf range.

This is NOT extension of an arbitrarily prescribed old map, not a
persistent successor through future horizons, and not countable
unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Pure finite-palette lemma: if each arbitrary high target
threshold has a genuine witness whose values on a FINITE old set
are bounded by B, then one COMPLETE old finite value profile can
be held fixed while witnesses remain arbitrarily high.

The witnesses can be any functions Nat -> Nat; no diary structure
or compactness of an infinite branching tree is assumed. -/
theorem cofinal_bounded_finite_set_profile_stabilizes
    (L : Finset Nat) (B : Nat)
    (Good : (Nat → Nat) → Nat → Prop)
    (hAll : ∀ M : Nat, ∃ v : Nat, ∃ g : Nat → Nat,
      M < v ∧ Good g v ∧
      ∀ a : Nat, a ∈ L → g a ≤ B) :
    ∃ v₀ : Nat, ∃ g₀ : Nat → Nat,
      Good g₀ v₀ ∧
      ∀ M : Nat, ∃ v : Nat, ∃ g : Nat → Nat,
        M < v ∧ Good g v ∧
        ∀ a : Nat, a ∈ L → g a = g₀ a := by
  classical
  let C := ({a : Nat // a ∈ L} → Fin (B + 1))
  let R : C → Nat → Prop := fun c M =>
    ∃ v : Nat, ∃ g : Nat → Nat,
      M < v ∧ Good g v ∧
      ∀ a : Nat, ∀ ha : a ∈ L,
        g a = (c ⟨a,ha⟩).val
  have hDown : ∀ (c : C) (M N : Nat),
      N ≤ M → R c M → R c N := by
    intro c M N hNM
    rintro ⟨v,g,hHigh,hGood,hCode⟩
    exact ⟨v,g,lt_of_le_of_lt hNM hHigh,hGood,hCode⟩
  have hCover : ∀ M : Nat, ∃ c : C,
      c ∈ (Finset.univ : Finset C) ∧ R c M := by
    intro M
    obtain ⟨v,g,hHigh,hGood,hOldBound⟩ := hAll M
    let c : C := fun a =>
      ⟨g a.val, by
        have hB : g a.val ≤ B := hOldBound a.val a.property
        omega⟩
    refine ⟨c,Finset.mem_univ _,v,g,hHigh,hGood,?_⟩
    intro a ha
    rfl
  obtain ⟨c,_hc,hRecur⟩ :=
    finite_choice_persistent_of_downward_type
      (Finset.univ : Finset C) R hDown hCover
  obtain ⟨v₀,g₀,_hV₀,hGood₀,hCode₀⟩ := hRecur 0
  refine ⟨v₀,g₀,hGood₀,?_⟩
  intro M
  obtain ⟨v,g,hHigh,hGood,hCode⟩ := hRecur M
  refine ⟨v,g,hHigh,hGood,?_⟩
  intro a ha
  calc
    g a = (c ⟨a,ha⟩).val := hCode a ha
    _ = g₀ a := (hCode₀ a ha).symm

/-- When complete genuine reserved next-stage witnesses occur
cofinally with all old leaf images in a FIXED finite outer index
set A, one FULL old reserved support map f is fixed across
arbitrarily late genuine next-stage witnesses. The marked roles,
mixed edges and nonedges and exact S1/S2 generators of f are
automatically fixed from agreement on ALL old selected leaves.

No old stage f was prescribed in advance. -/
theorem cofinal_reserved_next_stages_with_finite_old_range_fix_support
    {H K : Ordered3Graph Nat}
    (F : Nat → Nat) (m : Nat) (A : Finset Nat)
    (hAll : ∀ M : Nat, ∃ t : Nat, ∃ g : Nat → Nat,
      M < F t ∧
      ReservedDiaryStage H K F (m + 1) g ∧
      g m = F t ∧
      (∀ a : Nat, a ∈ countableDiaryLeafPrefix H m →
        ∃ i : Nat, i ∈ A ∧ g a = F i)) :
    ∃ f : Nat → Nat,
      ReservedDiaryStage H K F m f ∧
      (∀ M : Nat, ∃ t : Nat, ∃ g : Nat → Nat,
        M < F t ∧
        ReservedDiaryStage H K F (m + 1) g ∧
        CofinalDiaryStageCompatible H m f g ∧
        g m = F t) := by
  classical
  let L := countableDiaryLeafPrefix H m
  let B := A.sup F
  let Good : (Nat → Nat) → Nat → Prop := fun g v =>
    ∃ t : Nat,
      v = F t ∧
      ReservedDiaryStage H K F (m + 1) g ∧
      g m = F t ∧
      (∀ a : Nat, a ∈ L →
        ∃ i : Nat, i ∈ A ∧ g a = F i)
  have hCover : ∀ M : Nat, ∃ v : Nat, ∃ g : Nat → Nat,
      M < v ∧ Good g v ∧
      ∀ a : Nat, a ∈ L → g a ≤ B := by
    intro M
    obtain ⟨t,g,hHigh,Q,hNew,hOld⟩ := hAll M
    refine ⟨F t,g,hHigh,⟨t,rfl,Q,hNew,hOld⟩,?_⟩
    intro a ha
    obtain ⟨i,hi,hImage⟩ := hOld a ha
    have hSup : F i ≤ B :=
      Finset.le_sup (f := F) hi
    omega
  obtain ⟨v₀,g₀,hGood₀,hCoFinal⟩ :=
    cofinal_bounded_finite_set_profile_stabilizes L B Good hCover
  obtain ⟨t₀,hValue₀,Q₀,hNew₀,hOld₀⟩ := hGood₀
  have Pf : ReservedDiaryStage H K F m g₀ :=
    Q₀.restrict (by omega)
  refine ⟨g₀,Pf,?_⟩
  intro M
  obtain ⟨v,g,hHigh,hGood,hFixedLeaves⟩ := hCoFinal M
  obtain ⟨t,hValue,Q,hNew,hOld⟩ := hGood
  have hHighF : M < F t := by omega
  have hCompatibility : CofinalDiaryStageCompatible H m g₀ g :=
    Pf.1.successor_compatible_of_selected_leaf_agreement
      Q.1 hFixedLeaves
  exact ⟨t,g,hHighF,Q,hCompatibility,hNew⟩

/-- New positive relative EXISTENCE theorem for EVERY source
new-leaf stage with at least one old selected leaf.

Starting only from full source/target RoleDiaries and the original
unordered induced generic leaf range F, there exists SOME genuinely
reserved finite map f on the ENTIRE old canonical S_m support that
admits genuine relative reserved next-leaf realizations with new
image larger than every numerical bound. The map f, including all
old S1/S2 generator images, is literally the SAME for all bounds.

The proof is by contradiction from genuine padded finite-source
unavoidability IN EVERY induced generic subcopy and the generic
avoidance theorem for locally bounded FINITE OLD SETS.

No extension of an arbitrarily preselected f is asserted; no
selected next leaf is guaranteed to survive one further source
horizon. Countable unavoidability remains an open stronger target. -/
theorem RoleDiary.exists_some_fixed_old_support_with_unbounded_reserved_next_leaf
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (m : Nat) (hm : IsLeaf H m)
    (hOldNonempty : (countableDiaryLeafPrefix H m).Nonempty) :
    ∃ f : Nat → Nat,
      ReservedDiaryStage H K (fun t : Nat => F t) m f ∧
      (∀ M : Nat, ∃ t : Nat, ∃ g : Nat → Nat,
        M < F t ∧
        ReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g ∧
        CofinalDiaryStageCompatible H m f g ∧
        g m = F t) := by
  classical
  let L := countableDiaryLeafPrefix H m
  let R : Finset Nat → Nat → Prop := fun A y =>
    ∃ g : Nat → Nat,
      ReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g ∧
      g m = F y ∧
      (∀ a : Nat, a ∈ L →
        ∃ i : Nat, i ∈ A ∧ g a = F i)
  by_contra hNoStage
  have hBound : ∀ A : Finset Nat, ∃ B : Nat,
      ∀ y : Nat, B ≤ F y → ¬ R A y := by
    intro A
    by_contra hNoBound
    have hCofinal : ∀ M : Nat, ∃ t : Nat, ∃ g : Nat → Nat,
        M < F t ∧
        ReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g ∧
        g m = F t ∧
        (∀ a : Nat, a ∈ L →
          ∃ i : Nat, i ∈ A ∧ g a = F i) := by
      intro M
      by_contra hNoWitness
      apply hNoBound
      refine ⟨M + 1,?_⟩
      intro y hBy hRA
      obtain ⟨g,Q,hNew,hOld⟩ := hRA
      apply hNoWitness
      exact ⟨y,g,by omega,Q,hNew,hOld⟩
    obtain ⟨f,Pf,hAll⟩ :=
      cofinal_reserved_next_stages_with_finite_old_range_fix_support
        (fun t : Nat => F t) m A hCofinal
    exact hNoStage ⟨f,Pf,hAll⟩
  obtain ⟨u,hTargetMono,hAvoid⟩ :=
    GenericEnumerated3Graph.exists_generic_selfembedding_avoiding_finite_old_sets
      G (fun t : Nat => F t) F.injective R hBound
  have hUniversal : Ordered3Graph.CountablyUniversal G.graph := by
    intro J
    obtain ⟨v,hMono,hInduced⟩ :=
      G.exists_countable_induced_embedding J
    let e : Ordered3Graph.Embedding J G.graph := {
      toFun := v
      strictMono := hMono
      edge_iff := by
        intro a b c hab hbc
        exact hInduced a b c hab hbc
    }
    exact ⟨e.asUnordered⟩
  let FG : Ordered3Graph.UnorderedEmbedding G.graph K :=
    F.comp u.asUnordered
  have hFGLeaf (t : Nat) : IsLeaf K (FG t) := by
    change IsLeaf K (F (u t))
    exact hFLeaf (u t)
  obtain ⟨g,Q⟩ :=
    exists_independent_reserved_stage_in_universal_leaf_range
      DH DK G hUniversal FG hFGLeaf (m + 1)
  have hmSelected : m ∈ countableDiaryLeafPrefix H (m + 1) :=
    (mem_countableDiaryLeafPrefix_iff H (m + 1) m).mpr
      ⟨hm.1,by omega,hm⟩
  have hmSupport : m ∈ countableDiaryFiniteSupport H (m + 1) :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H (m + 1)) m hmSelected
  obtain ⟨j,hj⟩ := Q.1.leaf_range m hmSupport hm
  have hGJ : g m = F (u j) := hj
  let A : Finset Nat := (Finset.range j).image (fun i : Nat => u i)
  have hOldRange : ∀ a : Nat, a ∈ L →
      ∃ i : Nat, i ∈ A ∧ g a = F i := by
    intro a ha
    obtain ⟨_ha3,ham,haLeaf⟩ :=
      (mem_countableDiaryLeafPrefix_iff H m a).mp ha
    have haNext : a ∈ countableDiaryLeafPrefix H (m + 1) :=
      (countableDiaryLeafPrefix_mono H m (m + 1) (by omega)) ha
    have haSupport : a ∈ countableDiaryFiniteSupport H (m + 1) :=
      mem_finiteLeafMeetSupport_leaf H
        (countableDiaryLeafPrefix H (m + 1)) a haNext
    obtain ⟨i,hi⟩ := Q.1.leaf_range a haSupport haLeaf
    have hGI : g a = F (u i) := hi
    have hOrder : g a < g m :=
      Q.1.ordered a m haSupport hmSupport ham
    have hij : i < j := by
      by_contra hn
      have hji : j ≤ i := Nat.le_of_not_gt hn
      have hFle : F (u j) ≤ F (u i) :=
        hTargetMono.monotone hji
      omega
    have hiA : u i ∈ A :=
      Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr hij,rfl⟩
    exact ⟨u i,hiA,hGI⟩
  obtain ⟨a,ha⟩ := hOldNonempty
  obtain ⟨i,hi,_hOldi⟩ := hOldRange a ha
  have hANonempty : A.Nonempty := ⟨i,hi⟩
  have hEarlier : ∀ x : Nat, x ∈ A →
      ∃ i : Nat, i < j ∧ x = u i := by
    intro x hx
    obtain ⟨i,hi,hUI⟩ := Finset.mem_image.mp hx
    exact ⟨i,Finset.mem_range.mp hi,hUI.symm⟩
  have QOriginal :
      ReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g := by
    refine ⟨?_,Q.2⟩
    refine {
      ordered := Q.1.ordered
      marker_zero := Q.1.marker_zero
      marker_one := Q.1.marker_one
      marker_two := Q.1.marker_two
      leaf_role := Q.1.leaf_role
      one_split_role := Q.1.one_split_role
      two_split_role := Q.1.two_split_role
      induced_edge := Q.1.induced_edge
      leaf_oneMeet := Q.1.leaf_oneMeet
      leaf_twoMeet := Q.1.leaf_twoMeet
      leaf_range := ?_
    }
    intro x hx hLeaf
    obtain ⟨t,ht⟩ := Q.1.leaf_range x hx hLeaf
    exact ⟨u t,ht⟩
  have hRA : R A (u j) :=
    ⟨g,QOriginal,hGJ,hOldRange⟩
  exact (hAvoid j A hANonempty hEarlier) hRA

end DiaryLeafPriority
end ThreeUniformDiaries
