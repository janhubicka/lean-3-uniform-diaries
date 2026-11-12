import ThreeUniformDiaries.DiaryGenericLocallyFiniteForwardAvoidance
import ThreeUniformDiaries.DiaryIndependentReservedStageExistence
import ThreeUniformDiaries.DiaryReservedFiniteHorizonCompatibility
import ThreeUniformDiaries.DiarySecondLeafFavourableSplitCriterion

/-!
# Track D: finite diary unavoidability forces an unbounded second-leaf root

The generic avoidance theorem disproves a genuinely new obstruction:
suppose that, in a prescribed UNORDERED induced generic leaf range F,
each possible first source leaf image F(i) admits only finitely many
target-numerically later images F(j) that occur together in an
ACTUAL genuine reserved finite diary stage.

A generic induced selfcopy with NO such forward pair can then be
constructed, because the forbidden future-pair relation is locally
bounded. The composite F ∘ u is required to be INCREASING in target
order, although F itself is unordered.

But the independently verified finite-source unavoidability PLUS
complete-original-prefix padding supplies a full future-order-reserved
finite diary stage inside EVERY prescribed induced generic subcopy.
Two selected source leaves in that stage give exactly the forbidden
pair, a contradiction.

Thus for ANY earlier selected source leaf a and any later new source
leaf m there is SOME FIXED target value F(i) for a with arbitrarily
large genuine reserved stage images for m. Other earlier old images
are not fixed by this general first theorem.

When a is the ONLY earlier selected source leaf, the old support is
markers 0,1,2 and a. Fixing F(i) thus fixes the WHOLE old support,
and the verified favourable-root-split iff gives a genuinely
favourable recurrent target E2 split s with correct source right
orientation and both original numerical gap inequalities.

This closes the existence of SOME favourable root for the SECOND
selected source leaf. It does NOT prove extension of an ARBITRARY
preselected old root, nor persistence through any later horizon.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Two original generic SOURCE indices i,j occur together as the
images of one earlier source leaf a and the later new source leaf m
in some GENUINE reserved source-support stage inside the original
outer range F. All diary edges/nonedges, roles, numerical meets,
original range membership, and future reserve are already part of
the supplied stage. -/
def ReservedTwoLeafImagePair
    (H K : Ordered3Graph Nat)
    (F : Nat → Nat) (a m i j : Nat) : Prop :=
  ∃ g : Nat → Nat,
    ReservedDiaryStage H K F (m + 1) g ∧
    g a = F i ∧
    g m = F j

/-- Finite-source unavoidability inside EVERY induced generic
leaf subcopy rules out locally finite forward eligible pairs.

For any earlier selected genuine source leaf a<m and the NEW genuine
source leaf m, there is SOME fixed original F-index i such that,
for every target bound M, a GENUINE reserved stage on S_(m+1)
can map the old source leaf a to the SAME value F(i), while the
new leaf m has target image F(j)>M.

The remaining old selected source leaves may vary in these stages.
The special one-old-leaf corollary below will fix their whole support.
No preassigned old stage, E2 split, or countable fusion is assumed. -/
theorem RoleDiary.exists_old_leaf_image_with_unbounded_reserved_new_leaf
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (a m : Nat)
    (haSelected : a ∈ countableDiaryLeafPrefix H m)
    (hm : IsLeaf H m) :
    ∃ i : Nat, ∀ M : Nat, ∃ j : Nat, ∃ g : Nat → Nat,
      M < F j ∧
      ReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g ∧
      g a = F i ∧ g m = F j := by
  classical
  let R : Nat → Nat → Prop :=
    fun i j => ReservedTwoLeafImagePair H K (fun t : Nat => F t) a m i j
  by_contra hNoRoot
  have hFinite : ∀ i : Nat, ∃ B : Nat, ∀ j : Nat,
      B ≤ F j → ¬ R i j := by
    intro i
    by_contra hNoBound
    apply hNoRoot
    refine ⟨i,?_⟩
    intro M
    by_contra hNoWitness
    apply hNoBound
    refine ⟨M + 1,?_⟩
    intro j hj hR
    obtain ⟨g,Q,hGI,hGJ⟩ := hR
    exact hNoWitness ⟨j,g,by omega,Q,hGI,hGJ⟩
  obtain ⟨u,hFMono,hAvoid⟩ :=
    GenericEnumerated3Graph.exists_generic_selfembedding_avoiding_finite_forward
      G (fun t : Nat => F t) F.injective R hFinite
  have hUniversal : Ordered3Graph.CountablyUniversal G.graph := by
    intro L
    obtain ⟨h,hMono,hInduced⟩ := G.exists_countable_induced_embedding L
    let e : Ordered3Graph.Embedding L G.graph := {
      toFun := h
      strictMono := hMono
      edge_iff := by
        intro x y z hxy hyz
        exact hInduced x y z hxy hyz
    }
    exact ⟨e.asUnordered⟩
  let FG : Ordered3Graph.UnorderedEmbedding G.graph K :=
    F.comp u.asUnordered
  have hFGLeaf (t : Nat) : IsLeaf K (FG t) :=
    hFLeaf (u t)
  obtain ⟨g,Q⟩ :=
    exists_independent_reserved_stage_in_universal_leaf_range
      DH DK G hUniversal FG hFGLeaf (m + 1)
  have ham : a < m :=
    ((mem_countableDiaryLeafPrefix_iff H m a).mp haSelected).2.1
  have hLa : IsLeaf H a :=
    ((mem_countableDiaryLeafPrefix_iff H m a).mp haSelected).2.2
  have haNext : a ∈ countableDiaryLeafPrefix H (m + 1) :=
    (countableDiaryLeafPrefix_mono H m (m + 1) (by omega))
      haSelected
  have hmNext : m ∈ countableDiaryLeafPrefix H (m + 1) :=
    (mem_countableDiaryLeafPrefix_iff H (m + 1) m).mpr
      ⟨hm.1, by omega, hm⟩
  have haSupport : a ∈ countableDiaryFiniteSupport H (m + 1) :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H (m + 1)) a haNext
  have hmSupport : m ∈ countableDiaryFiniteSupport H (m + 1) :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H (m + 1)) m hmNext
  obtain ⟨i,hi⟩ := Q.1.leaf_range a haSupport hLa
  obtain ⟨j,hj⟩ := Q.1.leaf_range m hmSupport hm
  have hGOrder : g a < g m :=
    Q.1.ordered a m haSupport hmSupport ham
  have hGI : g a = F (u i) := hi
  have hGJ : g m = F (u j) := hj
  have hij : i < j := by
    by_contra hNot
    have hji : j ≤ i := Nat.le_of_not_gt hNot
    have hFOrder : F (u j) ≤ F (u i) := hFMono.monotone hji
    omega
  have QOriginal :
      ReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g := by
    refine ⟨?_, Q.2⟩
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
  have hChosen : R (u i) (u j) :=
    ⟨g,QOriginal,hGI,hGJ⟩
  exact (hAvoid i j hij) hChosen

/-- Specialise to the second selected source leaf m with unique old
selected source leaf a. The first generic leaf image F(i) can be
chosen so that one ACTUAL OLD reserved stage f is fixed on all of
its supported old vertices, while the next leaf has arbitrarily
high genuine reserved successors compatible with that same f.

This is independent of an arbitrary preselected old root. The
result does NOT assert that any selected successor persists through
even one later source horizon. -/
theorem RoleDiary.exists_chosen_first_leaf_with_unbounded_second_successors
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (a m : Nat)
    (ha : IsLeaf H a) (hm : IsLeaf H m) (ham : a < m)
    (hOld : countableDiaryLeafPrefix H m = {a}) :
    ∃ f : Nat → Nat,
      ReservedDiaryStage H K (fun t : Nat => F t) m f ∧
      (∃ i : Nat, f a = F i) ∧
      (∀ M : Nat, ∃ j : Nat, ∃ g : Nat → Nat,
        M < F j ∧
        ReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g ∧
        (∀ x : Nat, x ∈ countableDiaryFiniteSupport H m →
          g x = f x) ∧
        g m = F j) := by
  classical
  have haSelected : a ∈ countableDiaryLeafPrefix H m := by
    rw [hOld]
    simp
  obtain ⟨i,hAll⟩ :=
    DH.exists_old_leaf_image_with_unbounded_reserved_new_leaf
      DK G F hFLeaf a m haSelected hm
  obtain ⟨j0,g0,_hHigh0,Q0,hA0,_hM0⟩ := hAll 0
  let f := g0
  have Pf : ReservedDiaryStage H K (fun t : Nat => F t) m f :=
    Q0.restrict (by omega)
  refine ⟨f,Pf,⟨i,hA0⟩,?_⟩
  intro M
  obtain ⟨j,g,hHigh,Q,hA,hM⟩ := hAll M
  have hKeepLeaves : ∀ x : Nat,
      x ∈ countableDiaryLeafPrefix H m → g x = f x := by
    intro x hx
    have hEq : x = a := by
      rw [hOld] at hx
      simpa only [Finset.mem_singleton] using hx
    subst x
    exact hA.trans hA0.symm
  have hKeepFull : ∀ x : Nat,
      x ∈ countableDiaryFiniteSupport H m → g x = f x :=
    Pf.1.successor_compatible_of_selected_leaf_agreement
      Q.1 hKeepLeaves
  exact ⟨j,g,hHigh,Q,hKeepFull,hM⟩

/-- An UNCONDITIONAL positive selection of SOME favourable rooted
E2 split for the second source leaf in EVERY genuinely generic
prescribed target leaf copy. The selected first source leaf image
is allowed to vary; the ensuing OLD map f and actual target split s
are then fixed. The cofinal s-fibre meets the source right E2
orientation and BOTH fixed numerical gap constraints.

The only potentially unproved input is the separately checked
locally-finite generic avoidance lemma imported above; every other
component is previously kernel-verified finite unavoidability and
the exact rooted second-leaf criterion. No later-source persistence
or countable diary unavoidability follows. -/
theorem RoleDiary.exists_some_favourable_second_leaf_root_in_generic_range
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (a m : Nat)
    (ha : IsLeaf H a) (hm : IsLeaf H m) (ham : a < m)
    (hOld : countableDiaryLeafPrefix H m = {a}) :
    ∃ f : Nat → Nat,
      ReservedDiaryStage H K (fun t : Nat => F t) m f ∧
      ∃ s : Nat,
        IsOneSplit K s ∧
        s < f a ∧
        (∀ M : Nat, ∃ t : Nat,
          M < F t ∧ K.oneMeetLevel (f a) (F t) = s) ∧
        (H.edge 0 (H.oneMeetLevel a m) m ↔
          ¬ K.edge 0 s (f a)) ∧
        H.oneMeetLevel a m ≤ s ∧
        s + (a - H.oneMeetLevel a m) ≤ f a := by
  obtain ⟨f,Pf,_hOldInRange,hAll⟩ :=
    DH.exists_chosen_first_leaf_with_unbounded_second_successors
      DK G F hFLeaf a m ha hm ham hOld
  have hImmediate : ∀ M : Nat, ∃ t : Nat, ∃ g : Nat → Nat,
      M < F t ∧
      ReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g ∧
      (∀ u : Nat, u ∈ countableDiaryLeafPrefix H m →
        g u = f u) ∧
      g m = F t := by
    intro M
    obtain ⟨t,g,hHigh,Q,hKeep,hM⟩ := hAll M
    refine ⟨t,g,hHigh,Q,?_,hM⟩
    intro u hu
    have hSupp : u ∈ countableDiaryFiniteSupport H m :=
      mem_finiteLeafMeetSupport_leaf H
        (countableDiaryLeafPrefix H m) u hu
    exact hKeep u hSupp
  obtain ⟨s,hsRole,hsBelow,hCone,hBit,hGap1,hGap2⟩ :=
    (DH.second_leaf_unbounded_successors_iff_favourable_rooted_split
      DK (fun t : Nat => F t) f a m ha hm ham hOld
      Pf hFLeaf).mp hImmediate
  exact ⟨f,Pf,s,hsRole,hsBelow,hCone,hBit,hGap1,hGap2⟩

end DiaryLeafPriority
end ThreeUniformDiaries
