import ThreeUniformDiaries.DiaryCofinalGenericNewNewS2E3Profile
import ThreeUniformDiaries.DiaryOldLeafPairGenericSuccessor

/-!
# Track A: the complete one-new-leaf S2/E3 profile over an ACTUAL old stage

Take one genuine old reserved diary stage f whose selected old
source leaves are mapped into ONE original unordered induced copy F[G]
of the actual enumerated generic 3-hypergraph in genuine target leaves.
Fix the true next source leaf m.

The old leaf images W = f[L_m] are literal, not movable roots. The
prescribed target E5 pattern is likewise not chosen freely: it is
obtained from the SOURCE bits H.edge(a,b,m) for every ordered old
selected leaf pair. The actual old stage's strict increasing order
makes this pattern well-defined on old target leaf pairs, and
its range hypothesis makes all of them represented in F[G].

Apply the newly checked cofinal generic full pair profile theorem:
the SAME genuine leaves F(t) cofinally realize ALL source-required
old-pair E5 edges AND nonedges, one complete old-cut singleton
colour, fixed actual numeric S1/E2 root data and BOTH families of
S2 meet profiles with their genuine E3 branch signs:
  old-old vs old-new and old-new vs old-new.

The S1 and S2 vectors are existentially selected from the TARGET
and are NOT asserted to agree with source-required new generator
images. No full generator table functionality, exact source S1/S2
relative successor, future order reserve, fixed new leaf image,
all-horizon persistence or diary unavoidability follows.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Over a genuinely fixed old reserved stage, all required old-pair
E5 bits are realized cofinally together with one actual complete
target S1/E2/S2/E3 finite-root profile, including the old-new/
old-new pair-meet family just added.

The numeric target profile is SELECTED rather than source-prescribed;
this is a conditional geometric step, NOT a reserved successor. -/
theorem RoleDiary.exists_cofinal_old_stage_required_E5_full_target_pair_profile
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
        ∃ q : FiniteRootCrossPairMeetProfile W,
          ∃ r : FiniteRootNewNewPairMeetProfile W,
            (∀ w : {w : Nat // w ∈ W},
              IsOneSplit K (p w).val ∧ (p w).val < w.val) ∧
            (∀ ab : {ab : Nat × Nat // ab ∈ finiteOrderedLeafPairs W},
              ∀ w : {w : Nat // w ∈ W},
                (q ab w).val = min ab.val.1 w.val ∨
                (q ab w).val = 1 ∨ IsTwoSplit K (q ab w).val) ∧
            (∀ ab : {ab : Nat × Nat // ab ∈ finiteOrderedLeafPairs W},
              (r ab).val = min ab.val.1 ab.val.2 ∨
              (r ab).val = 1 ∨ IsTwoSplit K (r ab).val) ∧
            (∀ N M : Nat, ∃ t : Nat,
              N ≤ t ∧ M < F t ∧ B < F t ∧ IsLeaf K (F t) ∧
              DiaryLowerBoundColors.singletonColour K B (F t) = c ∧
              (∀ a b : Nat, a ∈ L → b ∈ L → a < b →
                (H.edge a b m ↔ K.edge (f a) (f b) (F t))) ∧
              (∀ w : {w : Nat // w ∈ W},
                K.oneMeetLevel w.val (F t) = (p w).val ∧
                (K.edge 0 (p w).val (F t) ↔
                  ¬ K.edge 0 (p w).val w.val)) ∧
              (∀ ab : {ab : Nat × Nat // ab ∈ finiteOrderedLeafPairs W},
                ∀ w : {w : Nat // w ∈ W},
                  K.twoMeetLevel ab.val.1 ab.val.2 w.val (F t) =
                    (q ab w).val ∧
                  (IsTwoSplit K (q ab w).val →
                    (K.edge (q ab w).val w.val (F t) ↔
                      ¬ K.edge (q ab w).val ab.val.1 ab.val.2))) ∧
              (∀ ab : {ab : Nat × Nat // ab ∈ finiteOrderedLeafPairs W},
                K.twoMeetLevel ab.val.1 (F t) ab.val.2 (F t) =
                  (r ab).val ∧
                (IsTwoSplit K (r ab).val →
                  (K.edge (r ab).val ab.val.1 (F t) ↔
                    ¬ K.edge (r ab).val ab.val.2 (F t))))) := by
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
  obtain ⟨c, p, q, r, hRoles, hCrossRoles, hNewRoles, hAll⟩ :=
    DK.exists_cofinal_generic_joint_complete_S2_E3_profile
      G F hFLeaf W hRoots B chi
  refine ⟨c, p, q, r, hRoles, hCrossRoles, hNewRoles, ?_⟩
  intro N M
  obtain ⟨t, htN, htM, htB, htLeaf,
      htColour, htPair, htRoot, htCross, htNewNew⟩ := hAll N M
  refine ⟨t, htN, htM, htB, htLeaf, htColour, ?_,
    htRoot, htCross, htNewNew⟩
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
