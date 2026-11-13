import ThreeUniformDiaries.DiaryUniformBoundedOldStageGenericAvoidance
import ThreeUniformDiaries.DiaryIndependentReservedStageExistence
import ThreeUniformDiaries.DiaryGenericFiniteOldSupportUnboundedNextLeaf

/-!
# Track D: genuine next-stage witnesses must move old supports under refinement

Let a<b be two genuine earlier selected source leaves and m a new
source leaf. For EVERY numerical bound B there is a WHOLE unordered
induced generic target-leaf refinement J of the ORIGINAL prescribed F
range such that any ACTUAL reserved stage Q on S_(m+1), relative to
the original F, with Q's new leaf image inside J, must send b to at
least B. This quantifies over ALL Q at once: old leaves are allowed to
lie anywhere in the original F range, not only in J.

There really is such a stage Q with its new leaf in J, since the
independent genuine finite-stage unavoidability theorem applies to J
and its actual generic source. The finite-stage leaf-range inclusion
lemma converts that J-stage back to the ORIGINAL F-range.

Thus old-support drift is both UNAVOIDABLE and NONVACUOUS in the
generic refinement chosen adversarially. No old support f is fixed
through all refinements; no image remains persistent through future
source horizons. In particular this theorem is not a countable
relative extension theorem or a failure of countable unavoidability.

Unlike the previously proved 'bad colour for a fixed f' theorem,
this new statement does not even choose an f before the refinement.
It directly exposes the necessary movement of all stage witnesses.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A genuine reserved finite diary stage can be regarded as a
stage for a LARGER prescribed target leaf range whenever EVERY
leaf in its former prescribed range also belongs to the latter.

The full marked edges/nonedges, exact S1/S2 meets, old support
order and future-order reserve do not change; only the existential
leaf-range witnesses are reindexed. -/
theorem ReservedDiaryStage.weaken_leaf_range
    {H K : Ordered3Graph Nat}
    {F J f : Nat → Nat} {n : Nat}
    (P : ReservedDiaryStage H K J n f)
    (hSub : ∀ t : Nat, ∃ s : Nat, J t = F s) :
    ReservedDiaryStage H K F n f := by
  refine ⟨?_, P.2⟩
  refine {
    ordered := P.1.ordered
    marker_zero := P.1.marker_zero
    marker_one := P.1.marker_one
    marker_two := P.1.marker_two
    leaf_role := P.1.leaf_role
    one_split_role := P.1.one_split_role
    two_split_role := P.1.two_split_role
    induced_edge := P.1.induced_edge
    leaf_oneMeet := P.1.leaf_oneMeet
    leaf_twoMeet := P.1.leaf_twoMeet
    leaf_range := ?_
  }
  intro x hx hLeaf
  obtain ⟨t, ht⟩ := P.1.leaf_range x hx hLeaf
  obtain ⟨s, hs⟩ := hSub t
  exact ⟨s, ht.trans hs⟩

/-- Direct all-witness version of the validated bounded-stage generic
E5 avoidance. For a suitable single genuine induced GENERIC J,
EVERY actual reserved next source stage Q with g(m) in J must
map b above B. Crucially Q is a stage for the ORIGINAL F range;
its old leaf images need not be in J.

The universal statement is conditional on a genuinely existing Q,
and so on its own would be vacuous. The following theorem supplies
a genuine Q in the same J. -/
theorem exists_generic_refinement_forcing_old_support_escape
    {H K : Ordered3Graph Nat}
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    {m a b : Nat}
    (hm : IsLeaf H m)
    (ha : a ∈ countableDiaryLeafPrefix H m)
    (hb : b ∈ countableDiaryLeafPrefix H m)
    (hab : a < b)
    (B M : Nat) :
    ∃ J : Ordered3Graph.UnorderedEmbedding G.graph K,
      (∀ n : Nat, M < J n ∧ IsLeaf K (J n) ∧
        ∃ t : Nat, J n = F t) ∧
      (∀ g : Nat → Nat,
        ReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g →
        ∀ n : Nat, g m = J n → B ≤ g b) := by
  classical
  obtain ⟨J, hRange, hAvoid⟩ :=
    exists_generic_leaf_subcopy_avoiding_all_bounded_old_stages
      G F hFLeaf hm ha hb hab B M
  refine ⟨J, ?_, ?_⟩
  · intro n
    exact ⟨(hRange n).1, (hRange n).2.2.1, (hRange n).2.2.2⟩
  · intro g Q n hNew
    by_contra hNot
    have hBound : g b < B := by omega
    have P : ReservedDiaryStage H K (fun t : Nat => F t) m g :=
      Q.restrict (Nat.le_succ m)
    have hCompatible : CofinalDiaryStageCompatible H m g g := by
      intro x hx
      rfl
    have hGood : HasCompatibleReservedNextLeaf H K
        (fun t : Nat => F t) g m (J n) :=
      ⟨g, Q, hCompatible, hNew⟩
    exact (hAvoid g P hBound n) hGood

/-- In every true full-diary instance, the all-witness escape
refinement is NONVACUOUS. For each B,M there exists one induced
unordered generic subcopy J contained in the original F range
such that EVERY possible genuine reserved next-stage map g whose
new image lies in J has g(b)>=B, AND there is AT LEAST ONE such g.

The existence of g follows from independently verified finite
unavoidability inside J and transport of the leaf-range witnesses
to F; it is not postulated. This is a finite-stage result, not an
all-later-source-horizons persistence theorem. -/
theorem RoleDiary.exists_nonvacuous_generic_refinement_forcing_old_support_escape
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    {m a b : Nat}
    (hm : IsLeaf H m)
    (ha : a ∈ countableDiaryLeafPrefix H m)
    (hb : b ∈ countableDiaryLeafPrefix H m)
    (hab : a < b)
    (B M : Nat) :
    ∃ J : Ordered3Graph.UnorderedEmbedding G.graph K,
      (∀ n : Nat, M < J n ∧ IsLeaf K (J n) ∧
        ∃ t : Nat, J n = F t) ∧
      (∀ g : Nat → Nat,
        ReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g →
        ∀ n : Nat, g m = J n → B ≤ g b) ∧
      (∃ g : Nat → Nat,
        ReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g ∧
        ∃ n : Nat, g m = J n) := by
  classical
  obtain ⟨J, hRange, hAll⟩ :=
    exists_generic_refinement_forcing_old_support_escape
      G F hFLeaf hm ha hb hab B M
  have hUniversal : Ordered3Graph.CountablyUniversal G.graph := by
    intro A
    obtain ⟨v, hvMono, hvEdge⟩ :=
      G.exists_countable_induced_embedding A
    let e : Ordered3Graph.Embedding A G.graph := {
      toFun := v
      strictMono := hvMono
      edge_iff := by
        intro x y z hxy hyz
        exact hvEdge x y z hxy hyz
    }
    exact ⟨e.asUnordered⟩
  have hJLeaf (t : Nat) : IsLeaf K (J t) :=
    (hRange t).2.1
  have hJInsideF (t : Nat) : ∃ i : Nat, J t = F i :=
    (hRange t).2.2
  obtain ⟨g, Q⟩ :=
    exists_independent_reserved_stage_in_universal_leaf_range
      DH DK G hUniversal J hJLeaf (m + 1)
  have hmSelected : m ∈ countableDiaryLeafPrefix H (m + 1) :=
    (mem_countableDiaryLeafPrefix_iff H (m + 1) m).mpr
      ⟨hm.1, Nat.lt_succ_self m, hm⟩
  have hmSupport : m ∈ countableDiaryFiniteSupport H (m + 1) :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H (m + 1)) m hmSelected
  obtain ⟨n, hn⟩ := Q.1.leaf_range m hmSupport hm
  have QOriginal :
      ReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g :=
    Q.weaken_leaf_range hJInsideF
  exact ⟨J, hRange, hAll, g, QOriginal, n, hn⟩

/-- There is a quantifier-correct RE-STABILIZATION after arbitrary
old-support drift: for every B,M choose ONE induced unordered generic
refinement J beyond M such that all actual next-stage witnesses with
new image in J must move the old leaf b to at least B; nevertheless,
one newly selected COMPLETE old reserved support f with f(b)>=B
has genuine compatible next-leaf images cofinally high INSIDE J.

The single f is chosen AFTER the refinement J, but BEFORE the
successor lower bound N. The compatible next stages still vary with N,
and NO fixed new-leaf image is asserted to survive later source
horizons. This does not contradict generic elimination of any
preassigned old f, nor prove countable diary unavoidability. -/
theorem RoleDiary.exists_refinement_with_drift_and_recurrent_fixed_old_support
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    {m a b : Nat}
    (hm : IsLeaf H m)
    (ha : a ∈ countableDiaryLeafPrefix H m)
    (hb : b ∈ countableDiaryLeafPrefix H m)
    (hab : a < b)
    (B M : Nat) :
    ∃ J : Ordered3Graph.UnorderedEmbedding G.graph K,
      (∀ n : Nat, M < J n ∧ IsLeaf K (J n) ∧
        ∃ t : Nat, J n = F t) ∧
      (∀ g : Nat → Nat,
        ReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g →
        ∀ n : Nat, g m = J n → B ≤ g b) ∧
      ∃ f : Nat → Nat,
        ReservedDiaryStage H K (fun t : Nat => F t) m f ∧
        B ≤ f b ∧
        (∀ N : Nat, ∃ t : Nat, ∃ g : Nat → Nat,
          N < J t ∧
          ReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g ∧
          CofinalDiaryStageCompatible H m f g ∧
          g m = J t) := by
  classical
  obtain ⟨J, hRange, hForce⟩ :=
    exists_generic_refinement_forcing_old_support_escape
      G F hFLeaf hm ha hb hab B M
  have hJLeaf (t : Nat) : IsLeaf K (J t) :=
    (hRange t).2.1
  have hJInF (t : Nat) : ∃ i : Nat, J t = F i :=
    (hRange t).2.2
  obtain ⟨f, Pf, hRec⟩ :=
    DH.exists_some_fixed_old_support_with_unbounded_reserved_next_leaf
      DK G J hJLeaf m hm (⟨a, ha⟩)
  have PfOriginal :
      ReservedDiaryStage H K (fun t : Nat => F t) m f :=
    Pf.weaken_leaf_range hJInF
  have hbSupport : b ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H m) b hb
  have hfBound : B ≤ f b := by
    obtain ⟨t, g, _hAbove, Q, hOld, hNew⟩ := hRec 0
    have QOriginal :
        ReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g :=
      Q.weaken_leaf_range hJInF
    have hBound : B ≤ g b := hForce g QOriginal t hNew
    rw [hOld b hbSupport] at hBound
    exact hBound
  refine ⟨J, hRange, hForce, f, PfOriginal, hfBound, ?_⟩
  intro N
  obtain ⟨t, g, hHigh, Q, hOld, hNew⟩ := hRec N
  exact ⟨t, g, hHigh, Q.weaken_leaf_range hJInF, hOld, hNew⟩


end DiaryLeafPriority
end ThreeUniformDiaries
