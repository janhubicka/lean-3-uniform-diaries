import ThreeUniformDiaries.DiaryGenericTargetOldE5PatternCopy
import ThreeUniformDiaries.DiaryOldStageFullS2E3CofinalProfile

/-!
# Track A: one WHOLE generic target copy realizes source-required old E5 bits

The new generic target-coordinate bounded-pair pattern theorem
produces entire induced generic target leaf copies with arbitrary
prescribed positive and negative E5 incidence to every old target
pair in the original unordered generic range below a fixed cut.

Apply that theorem to one ACTUAL fixed old reserved source diary
stage P at level m, and take the target mask chi to be precisely
the SOURCE-required old-pair/new-leaf bits H.edge a b m.
Old-stage strict order on the finite selected old leaves implies
that chi is well-defined on the target images f(a), and its
leaf-range field puts all such old images in the ORIGINAL F[G].
The cut B=1+sup old selected leaf images contains them all.

Consequently there exists an ENTIRE induced unordered generic
true-leaf subcopy J[G] of the ORIGINAL prescribed F range,
arbitrarily far out numerically, such that EVERY vertex J(n)
realizes EVERY source-required E5 edge AND nonedge for the new
source leaf m against all pairs of old selected source leaves.

This is a positive relative leaf-only E5 reservoir and
complements the verified bad generic refinement obstruction:
both the prescribed GOOD E5 pattern and an incompatible E5
pattern contain genuine induced generic subcopies. The actual
obstruction is the JOINT realization of source-required numeric
S1/S2 generator positions, E2/E3 signs, target order/reserve,
and persistent next-leaf image in the SAME chosen range.

No full target RoleDiary hypothesis beyond the genuine OLD stage
is needed to realize the E5 pattern in one unordered generic
true-leaf copy; no full relative successor is constructed here.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- For one ACTUAL old reserved diary stage P whose selected
old source leaves are mapped into the original unordered induced
generic true-leaf target copy F[G], and for any target cutoff M,
there exists an ENTIRE induced generic true-leaf copy J[G]
inside F[G] above M such that EVERY J vertex realizes all
literal source-required old-pair E5 positive and negative bits.

The old f images are fixed and are not remapped. J need not
preserve target enumeration order. This theorem makes no S1/S2
or E2/E3 source compatibility claim. -/
theorem ReservedDiaryStage.exists_generic_leaf_subcopy_realizing_all_required_old_E5
    {H K : Ordered3Graph Nat}
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    {m : Nat} (f : Nat → Nat)
    (P : ReservedDiaryStage H K F m f)
    (M : Nat) :
    ∃ J : Ordered3Graph.UnorderedEmbedding G.graph K,
      (∀ n : Nat, M < J n ∧ IsLeaf K (J n) ∧
        ∃ t : Nat, J n = F t) ∧
      (∀ n a b : Nat,
        a ∈ countableDiaryLeafPrefix H m →
        b ∈ countableDiaryLeafPrefix H m →
        a < b →
        (H.edge a b m ↔ K.edge (f a) (f b) (J n))) := by
  classical
  let L := countableDiaryLeafPrefix H m
  let B := L.sup f + 1
  let chi : Nat → Nat → Bool := fun x y =>
    decide (∃ a b : Nat,
      a ∈ L ∧ b ∈ L ∧ a < b ∧
      f a = x ∧ f b = y ∧ H.edge a b m)
  have hLeafSupport (a : Nat) (ha : a ∈ L) :
      a ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H L a ha
  have hLeaf (a : Nat) (ha : a ∈ L) : IsLeaf H a :=
    ((mem_countableDiaryLeafPrefix_iff H m a).mp ha).2.2
  have hInj : ∀ a b : Nat, a ∈ L → b ∈ L →
      f a = f b → a = b := by
    intro a b ha hb hEq
    rcases lt_trichotomy a b with hlt | hSame | hgt
    · have hOrdered :=
        P.1.ordered a b (hLeafSupport a ha) (hLeafSupport b hb) hlt
      omega
    · exact hSame
    · have hOrdered :=
        P.1.ordered b a (hLeafSupport b hb) (hLeafSupport a ha) hgt
      omega
  obtain ⟨J, hRange, hPattern⟩ :=
    exists_generic_leaf_subcopy_in_prescribed_target_bounded_E5_pattern
      G K F hFLeaf B M chi
  refine ⟨J, ?_, ?_⟩
  · intro n
    obtain ⟨hM, _hB, hLeafN, t, ht⟩ := hRange n
    exact ⟨hM, hLeafN, t, ht⟩
  · intro n a b ha hb hab
    have hfa := hLeafSupport a ha
    have hfb := hLeafSupport b hb
    have hOrder : f a < f b :=
      P.1.ordered a b hfa hfb hab
    obtain ⟨i, hi⟩ := P.1.leaf_range a hfa (hLeaf a ha)
    obtain ⟨j, hj⟩ := P.1.leaf_range b hfb (hLeaf b hb)
    have hB : f b < B :=
      lt_of_le_of_lt (Finset.le_sup (f := f) hb)
        (Nat.lt_succ_self _)
    have hTargetOrder : F i < F j := by
      simpa only [←hi, ←hj] using hOrder
    have hTargetBound : F j < B := by
      simpa only [←hj] using hB
    have hActual :
        K.edge (f a) (f b) (J n) ↔
          chi (f a) (f b) = true := by
      simpa only [hi,hj] using
        hPattern n i j hTargetOrder hTargetBound
    have hChi :
        chi (f a) (f b) = true ↔ H.edge a b m := by
      change
        decide (∃ x y : Nat,
          x ∈ L ∧ y ∈ L ∧ x < y ∧
          f x = f a ∧ f y = f b ∧ H.edge x y m) = true ↔
          H.edge a b m
      simp only [decide_eq_true_eq]
      constructor
      · rintro ⟨x,y,hx,hy,hxy,hfx,hfy,he⟩
        have hxa : x = a := hInj x a hx ha hfx
        have hyb : y = b := hInj y b hy hb hfy
        simpa only [hxa, hyb] using he
      · intro he
        exact ⟨a,b,ha,hb,hab,rfl,rfl,he⟩
    exact hChi.symm.trans hActual.symm

end DiaryLeafPriority
end ThreeUniformDiaries
