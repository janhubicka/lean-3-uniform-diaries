import ThreeUniformDiaries.DiaryGenericRefinementForcesOldSupportEscape

/-!
# Track D: complete fixed old support with cofinal new images at ANY given future horizon

The checked finite-old-set generic avoidance proof is horizon-independent:
if no whole old support admitted cofinally late actual reserved witnesses at
ONE fixed source horizon q≥m+1, the forbidden relation R(A,y) for finite
old target leaf index sets A would be locally target-bounded. Its generic
avoidance selfcopy then contradicts independently checked genuine reserved
finite-stage existence at the SAME q.

The full finite old S1/S2 support can be fixed because a bounded finite
range of old selected leaves has only finitely many complete leaf vectors.
The source generator determinacy lemma upgrades selected-leaf equality
to equality on all of S_m. No fixed new image survives future horizons.

Both q and source m are fixed BEFORE the old support f is selected.
Different choices q may require DIFFERENT old maps f; no common
f for all q is constructed or claimed. In particular this is NOT
countable unavoidability, persistent successor, nor compactness.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- One finite old leaf image range whose genuine reserved q-horizon
new-leaf images recur cofinally yields ONE literally fixed complete
old support f, with q≥m+1. The q-horizon maps still vary with M. -/
theorem cofinal_reserved_horizon_stages_with_finite_old_range_fix_support
    {H K : Ordered3Graph Nat}
    (F : Nat → Nat) (m q : Nat) (hmq : m + 1 ≤ q) (A : Finset Nat)
    (hAll : ∀ M : Nat, ∃ t : Nat, ∃ g : Nat → Nat,
      M < F t ∧
      ReservedDiaryStage H K F q g ∧
      g m = F t ∧
      (∀ a : Nat, a ∈ countableDiaryLeafPrefix H m →
        ∃ i : Nat, i ∈ A ∧ g a = F i)) :
    ∃ f : Nat → Nat,
      ReservedDiaryStage H K F m f ∧
      (∀ M : Nat, ∃ t : Nat, ∃ g : Nat → Nat,
        M < F t ∧
        ReservedDiaryStage H K F q g ∧
        CofinalDiaryStageCompatible H m f g ∧
        g m = F t) := by
  classical
  let L := countableDiaryLeafPrefix H m
  let B := A.sup F
  let Good : (Nat → Nat) → Nat → Prop := fun g v =>
    ∃ t : Nat,
      v = F t ∧
      ReservedDiaryStage H K F q g ∧
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
      (Q.restrict (by omega)).1 hFixedLeaves
  exact ⟨t,g,hHighF,Q,hCompatibility,hNew⟩


/-- For every finite source horizon q≥m+1 after a genuine source
new leaf m with nonempty old selected prefix, select ONE complete
reserved old support f for which actual q-horizon reserved maps over
f have arbitrarily high new-leaf images in the ORIGINAL unordered
generic target leaf range. The old support may depend on q. -/
theorem RoleDiary.exists_some_fixed_old_support_with_unbounded_new_leaf_at_horizon
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (m q : Nat) (hmq : m + 1 ≤ q) (hm : IsLeaf H m)
    (hOldNonempty : (countableDiaryLeafPrefix H m).Nonempty) :
    ∃ f : Nat → Nat,
      ReservedDiaryStage H K (fun t : Nat => F t) m f ∧
      (∀ M : Nat, ∃ t : Nat, ∃ g : Nat → Nat,
        M < F t ∧
        ReservedDiaryStage H K (fun t : Nat => F t) q g ∧
        CofinalDiaryStageCompatible H m f g ∧
        g m = F t) := by
  classical
  let L := countableDiaryLeafPrefix H m
  let R : Finset Nat → Nat → Prop := fun A y =>
    ∃ g : Nat → Nat,
      ReservedDiaryStage H K (fun t : Nat => F t) q g ∧
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
        ReservedDiaryStage H K (fun t : Nat => F t) q g ∧
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
      cofinal_reserved_horizon_stages_with_finite_old_range_fix_support
        (fun t : Nat => F t) m q hmq A hCofinal
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
      DH DK G hUniversal FG hFGLeaf q
  have hmSelected : m ∈ countableDiaryLeafPrefix H q :=
    (mem_countableDiaryLeafPrefix_iff H q m).mpr
      ⟨hm.1,by omega,hm⟩
  have hmSupport : m ∈ countableDiaryFiniteSupport H q :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H q) m hmSelected
  obtain ⟨j,hj⟩ := Q.1.leaf_range m hmSupport hm
  have hGJ : g m = F (u j) := hj
  let A : Finset Nat := (Finset.range j).image (fun i : Nat => u i)
  have hOldRange : ∀ a : Nat, a ∈ L →
      ∃ i : Nat, i ∈ A ∧ g a = F i := by
    intro a ha
    obtain ⟨_ha3,ham,haLeaf⟩ :=
      (mem_countableDiaryLeafPrefix_iff H m a).mp ha
    have haNext : a ∈ countableDiaryLeafPrefix H q :=
      (countableDiaryLeafPrefix_mono H m q (by omega)) ha
    have haSupport : a ∈ countableDiaryFiniteSupport H q :=
      mem_finiteLeafMeetSupport_leaf H
        (countableDiaryLeafPrefix H q) a haNext
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
      ReservedDiaryStage H K (fun t : Nat => F t) q g := by
    exact Q.weaken_leaf_range (fun t : Nat => ⟨u t, rfl⟩)
  have hRA : R A (u j) :=
    ⟨g,QOriginal,hGJ,hOldRange⟩
  exact (hAvoid j A hANonempty hEarlier) hRA

end DiaryLeafPriority
end ThreeUniformDiaries
