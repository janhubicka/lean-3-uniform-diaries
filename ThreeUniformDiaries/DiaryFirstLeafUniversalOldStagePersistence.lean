import ThreeUniformDiaries.DiaryFirstLeafEntireReservedSuccessorTail
import ThreeUniformDiaries.DiaryFirstLeafUniformAllHorizonColour
import ThreeUniformDiaries.DiaryGenericTargetOldE5PatternCopy

/-!
# Track A: ONE generic first-leaf tail works for EVERY genuine old reserved stage

Independent English proof and adversarial API repair:
3-uniform-diaries PR #368.

The first-leaf full-tail theorem already verified in Lean #1513
selects ONE first-leaf old marker stage f0 and ONE numerical
threshold T for which every genuine F-range leaf w≥T has an
actual reserved immediate successor over f0.

At the FIRST source leaf, the OLD selected-leaf prefix is EMPTY.
For ANY OTHER genuine old stage P at that same source m, the
verified successor_compatible_of_selected_leaf_agreement theorem
upgrades vacuous old leaf agreement with the SAME reserved
successor map to literal agreement on the complete S_m support.
Thus the SAME T works for ALL genuine old stages P.

The actual target-bounded generic old-E5 theorem can choose
ONE induced unordered generic subcopy J⊆F[G] above max(M,T),
BEFORE any old f,P is specified. EVERY J vertex then has
an actual compatible immediate reserved successor for EVERY P.

Independently, the verified all-horizon cofinally high reserved
stage existence theorem #1507 provides genuine q=m+1+n stages
at arbitrarily high target images, again compatible with ANY old
marker-only P. Hence EVERY old first-leaf stage is finitely
persistent and cofinally recurrent through ALL future horizons.

CRITICAL: the older direct first-leaf reserved-successor existence
API does NOT expose the equation g(m)=the specified F(t), so
we DO NOT claim a numerical threshold exactly m. The common
threshold T is verified by the exported full-tail theorem.
Nor does this give ONE fixed new image persistent through all
future horizons or countable diary unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Uniform FIRST-LEAF tail: one finite threshold T, depending only
on the original full diaries and prescribed generic leaf range,
works for EVERY genuine old reserved stage P at m.

Every true F-range leaf w≥T admits a complete genuine
FutureOrderReserve next stage, literally compatible with the
FULL old support map f of P. T is selected BEFORE f and P.
No target numerical monotonicity of F is assumed. -/
theorem RoleDiary.exists_first_leaf_tail_uniform_over_all_old_stages
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (m : Nat) (hm : IsLeaf H m)
    (hFirst : countableDiaryLeafPrefix H m = ∅) :
    ∃ T : Nat,
      ∀ (f : Nat → Nat),
        ReservedDiaryStage H K (fun t : Nat => F t) m f →
        ∀ w : Nat, T ≤ w → IsLeaf K w →
          (∃ t : Nat, w = F t) →
          HasCompatibleReservedNextLeaf H K
            (fun t : Nat => F t) f m w := by
  classical
  obtain ⟨f₀, P₀, T, hFullTail⟩ :=
    DH.exists_first_leaf_entire_late_reserved_successor_tail
      DK G F hFLeaf m hm hFirst
  refine ⟨T, ?_⟩
  intro f P w hT hw hRange
  obtain ⟨g, Q, _hOld₀, hAt⟩ :=
    hFullTail w hT hw hRange
  have hLeaves : ∀ u : Nat,
      u ∈ countableDiaryLeafPrefix H m → g u = f u := by
    intro u hu
    have hNo : u ∉ countableDiaryLeafPrefix H m := by
      simp [hFirst]
    exact False.elim (hNo hu)
  have hOld : CofinalDiaryStageCompatible H m f g :=
    P.1.successor_compatible_of_selected_leaf_agreement Q.1 hLeaves
  exact ⟨g, Q, hOld, hAt⟩

/-- FIRST-LEAF simultaneous generic cone:
for every target cutoff M, ONE ACTUAL unordered induced generic
target leaf subcopy J of the ORIGINAL F[G] is selected BEFORE
all possible legal old marker-stage maps f. ALL vertices of
J are genuine compatible reserved immediate next-leaf images
for EVERY old reserved stage P at m.

The universal quantifier over old P follows from marker-only
support determinacy. Neither J nor F must be target-increasing.
This is NOT one common new image at later source horizons. -/
theorem RoleDiary.exists_first_leaf_generic_cone_uniform_over_all_old_stages
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (m : Nat) (hm : IsLeaf H m)
    (hFirst : countableDiaryLeafPrefix H m = ∅) :
    ∀ M : Nat,
      ∃ J : Ordered3Graph.UnorderedEmbedding G.graph K,
        (∀ n : Nat, M < J n ∧ IsLeaf K (J n) ∧
          ∃ t : Nat, J n = F t) ∧
        (∀ (f : Nat → Nat),
          ReservedDiaryStage H K (fun t : Nat => F t) m f →
          ∀ n : Nat,
            HasCompatibleReservedNextLeaf H K
              (fun t : Nat => F t) f m (J n)) := by
  classical
  obtain ⟨T, hTail⟩ :=
    DH.exists_first_leaf_tail_uniform_over_all_old_stages
      DK G F hFLeaf m hm hFirst
  intro M
  obtain ⟨J, hRange, _hMask⟩ :=
    exists_generic_leaf_subcopy_in_prescribed_target_bounded_E5_pattern
      G K F hFLeaf 0 (max M T) (fun _ _ => false)
  refine ⟨J, ?_, ?_⟩
  · intro n
    exact ⟨lt_of_le_of_lt (le_max_left M T) (hRange n).1,
      (hRange n).2.2.1, (hRange n).2.2.2⟩
  · intro f P n
    have hT : T ≤ J n :=
      (le_max_right M T).trans (hRange n).1.le
    exact hTail f P (J n) hT
      (hRange n).2.2.1 (hRange n).2.2.2

/-- EVERY genuine reserved OLD marker stage P at the FIRST source
leaf m is finitely persistent, and cofinally high actual
reserved q=m+1+n horizon witnesses exist over its literal
old support at EVERY horizon n and numerical bound M.

This is universal in P, unlike the older existence of just
ONE old f. The compatible q-horizon witness may vary with
n,M and its new leaf image g(m) is NOT fixed. -/
theorem RoleDiary.first_leaf_every_old_stage_persistent_and_cofinally_recurrent
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (m : Nat) (hm : IsLeaf H m)
    (hFirst : countableDiaryLeafPrefix H m = ∅)
    (f : Nat → Nat)
    (P : ReservedDiaryStage H K (fun t : Nat => F t) m f) :
    PersistentReservedDiaryStage H K
      (fun t : Nat => F t) m f ∧
    (∀ n M : Nat,
      ∃ t : Nat, ∃ g : Nat → Nat,
        M < F t ∧
        ReservedDiaryStage H K (fun t : Nat => F t)
          (m + 1 + n) g ∧
        CofinalDiaryStageCompatible H m f g ∧
        g m = F t) := by
  classical
  have hIndependent : ∀ n M : Nat,
      ∃ t : Nat, ∃ g : Nat → Nat,
        M < F t ∧
        ReservedDiaryStage H K (fun t : Nat => F t)
          (m + 1 + n) g ∧
        g m = F t :=
    DH.exists_cofinally_high_reserved_new_image_at_every_finite_horizon
      DK G F hFLeaf m hm
  have hCompatible : ∀ n M : Nat,
      ∃ t : Nat, ∃ g : Nat → Nat,
        M < F t ∧
        ReservedDiaryStage H K (fun t : Nat => F t)
          (m + 1 + n) g ∧
        CofinalDiaryStageCompatible H m f g ∧
        g m = F t := by
    intro n M
    obtain ⟨t, g, hHigh, Q, hAt⟩ := hIndependent n M
    have QImmediate :
        ReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g :=
      Q.restrict (by omega)
    have hLeaves : ∀ u : Nat,
        u ∈ countableDiaryLeafPrefix H m → g u = f u := by
      intro u hu
      have hNo : u ∉ countableDiaryLeafPrefix H m := by
        simp [hFirst]
      exact False.elim (hNo hu)
    have hKeep : CofinalDiaryStageCompatible H m f g :=
      P.1.successor_compatible_of_selected_leaf_agreement
        QImmediate.1 hLeaves
    exact ⟨t, g, hHigh, Q, hKeep, hAt⟩
  have hPersistent : PersistentReservedDiaryStage H K
      (fun t : Nat => F t) m f := by
    refine ⟨P, ?_⟩
    intro n
    obtain ⟨t, g, _hHigh, Q, hOld, _hAt⟩ :=
      hCompatible n 0
    exact ⟨g, Q.restrict (by omega), hOld⟩
  exact ⟨hPersistent, hCompatible⟩

end DiaryLeafPriority
end ThreeUniformDiaries
