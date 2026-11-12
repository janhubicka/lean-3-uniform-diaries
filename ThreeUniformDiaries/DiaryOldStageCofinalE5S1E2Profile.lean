import ThreeUniformDiaries.DiaryCofinalGenericE5RootS1E2Sign
import ThreeUniformDiaries.DiaryOldLeafPairGenericSuccessor

/-!
# Track A: joint E5 / S1 / E2 cofinal geometry over one ACTUAL old diary stage

The general cofinal geometric theorem provides the same genuine
new target leaves satisfying an arbitrary finite old-pair E5
pattern, one full mixed singleton colour, and one fixed
actual numeric S1/E2 profile over a finite set of old target roots.

Here the old roots and the desired E5 bits are NOT external:
take the old leaf images of an ACTUAL reserved stage f as the
root family W, and prescribe the literal edge/nonedge bits
H.edge a b m of the new source leaf m against every old
selected source pair a<b. Since f is ordered and maps genuine
old leaves into one fixed unordered generic target leaf copy,
the old-pair target pattern is well-defined and is covered
by the verified generic extension theorem.

We obtain one full colour and one target root S1/E2 profile
cofinally realized together with ALL source-required old-pair
E5 edges and nonedges in the original prescribed generic
leaf range. The S1/E2 profile is selected existentially
and is not claimed to equal the source-prescribed new generator
table. This is not a reserved successor or no-escape theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- For an ACTUAL old reserved stage in an arbitrary unordered
generic true-leaf target copy, there is one cofinally
realized full mixed colour and one fixed genuine numeric
S1/E2 vector at every old target leaf, all on the SAME
genuine new-leaf candidates satisfying the entire required
old-leaf-pair E5 table of source m.

This does not show the chosen split profile is favourable
for the source's prescribed one-splits, nor any mixed E3,
S2 generator collisions, order reserve, or persistent image. -/
theorem RoleDiary.exists_cofinal_old_stage_E5_and_root_S1_E2_profile
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (m : Nat) (f : Nat → Nat)
    (P : ReservedDiaryStage H K F m f)
    (hm : IsLeaf H m) :
    let L := countableDiaryLeafPrefix H m
    let B := L.sup f + 1
    let W := L.image f
    ∃ c : Fin B → Fin B → Bool,
      ∃ p : FiniteRootMeetProfile W,
        (∀ w : {w : Nat // w ∈ W},
          IsOneSplit K (p w).val ∧ (p w).val < w.val) ∧
        (∀ N M : Nat, ∃ t : Nat,
          N ≤ t ∧ M < F t ∧ B < F t ∧ IsLeaf K (F t) ∧
          DiaryLowerBoundColors.singletonColour K B (F t) = c ∧
          (∀ a b : Nat, a ∈ L → b ∈ L → a < b →
            (H.edge a b m ↔ K.edge (f a) (f b) (F t))) ∧
          (∀ w : {w : Nat // w ∈ W},
            K.oneMeetLevel w.val (F t) = (p w).val ∧
            (K.edge 0 (p w).val (F t) ↔
              ¬ K.edge 0 (p w).val w.val))) := by
  classical
  let L := countableDiaryLeafPrefix H m
  let B := L.sup f + 1
  let W := L.image f
  let chi : Nat → Nat → Bool := fun x y =>
    decide (∃ a b : Nat,
      a ∈ L ∧ b ∈ L ∧ a < b ∧
      f a = x ∧ f b = y ∧ H.edge a b m)
  have hLeafSupport (a : Nat) (ha : a ∈ L) :
      a ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H L a ha
  have hLeaf (a : Nat) (ha : a ∈ L) : IsLeaf H a :=
    ((mem_countableDiaryLeafPrefix_iff H m a).mp ha).2.2
  have hRoots (w : Nat) (hw : w ∈ W) : IsLeaf K w := by
    obtain ⟨a, ha, hfa⟩ := Finset.mem_image.mp hw
    have hTarget := P.1.leaf_role a
      (hLeafSupport a ha) (hLeaf a ha)
    simpa only [hfa] using hTarget
  have hInj : ∀ a b : Nat, a ∈ L → b ∈ L →
      f a = f b → a = b := by
    intro a b ha hb hEq
    rcases lt_trichotomy a b with hlt | hSame | hgt
    · have hOrdered := P.1.ordered a b
        (hLeafSupport a ha) (hLeafSupport b hb) hlt
      omega
    · exact hSame
    · have hOrdered := P.1.ordered b a
        (hLeafSupport b hb) (hLeafSupport a ha) hgt
      omega
  obtain ⟨c, p, hRoles, hAll⟩ :=
    DK.exists_cofinal_generic_E5_pattern_and_finiteRoot_S1_E2
      G F hFLeaf W hRoots B chi
  refine ⟨c, p, hRoles, ?_⟩
  intro N M
  obtain ⟨t, htN, htM, htB, htLeaf,
      htColour, htPair, htProfile⟩ := hAll N M
  refine ⟨t, htN, htM, htB, htLeaf, htColour, ?_, htProfile⟩
  intro a b ha hb hab
  have hfa : a ∈ countableDiaryFiniteSupport H m :=
    hLeafSupport a ha
  have hfb : b ∈ countableDiaryFiniteSupport H m :=
    hLeafSupport b hb
  have hOrder : f a < f b :=
    P.1.ordered a b hfa hfb hab
  obtain ⟨i, hi⟩ := P.1.leaf_range a hfa (hLeaf a ha)
  obtain ⟨j, hj⟩ := P.1.leaf_range b hfb (hLeaf b hb)
  have hB : f b < B :=
    lt_of_le_of_lt (Finset.le_sup (f := f) hb)
      (Nat.lt_succ_self _)
  have hTargetOrder : F i < F j := by
    simpa only [← hi, ← hj] using hOrder
  have hTargetBound : F j < B := by
    simpa only [← hj] using hB
  have hActual :
      K.edge (f a) (f b) (F t) ↔
        chi (f a) (f b) = true := by
    simpa only [hi, hj] using
      htPair i j hTargetOrder hTargetBound
  have hChi :
      chi (f a) (f b) = true ↔ H.edge a b m := by
    change
      decide (∃ x y : Nat,
        x ∈ L ∧ y ∈ L ∧ x < y ∧
        f x = f a ∧ f y = f b ∧ H.edge x y m) = true ↔
        H.edge a b m
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨x, y, hx, hy, hxy, hfx, hfy, he⟩
      have hxa : x = a := hInj x a hx ha hfx
      have hyb : y = b := hInj y b hy hb hfy
      simpa only [hxa, hyb] using he
    · intro he
      exact ⟨a, b, ha, hb, hab, rfl, rfl, he⟩
  exact hChi.symm.trans hActual.symm

end DiaryLeafPriority
end ThreeUniformDiaries
