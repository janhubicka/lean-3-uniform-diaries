import ThreeUniformDiaries.DiarySingletonColourTailReplacement
import ThreeUniformDiaries.DiaryFullNewGeneratorProfileStabilisation

/-!
# Track D: a uniform old-stage tail cut and complete finite-horizon colour

The cut used for comparing the mixed singleton types of prospective
new target leaves can be fixed BEFORE choosing the new leaf or the
new nonleaf split-generator images.  It depends only on the already
fixed old finite support map f.

All newly generated nonleaf images lie below the supremum of old
selected-leaf images, and the old support images are fixed.
Consequently every compatible successor has all its supported images
other than the next leaf strictly below one common numerical cut.

The finite-horizon profile-stabilisation lemma can therefore be
strengthened: one COMPLETE new nonleaf-generator record AND one
COMPLETE mixed singleton-type colour at the common cut occur together
at every finite horizon.

The target leaf image itself can still escape every finite bound.
Neither finite-colour stabilisation nor tail replacement establishes
a coherent countable diary embedding.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A single cut fixed from the OLD supported images and OLD selected
leaf images. It does not depend on the image of the new leaf, nor
on the choice of its new split-generator image record. -/
noncomputable def oldStageTailCut
    (H : Ordered3Graph Nat) (m : Nat) (f : Nat → Nat) : Nat :=
  max ((countableDiaryFiniteSupport H m).sup f)
      ((countableDiaryLeafPrefix H m).sup f) + 1

/-- Every compatible reserved successor at a genuine leaf m has all
supported target images OTHER than g(m) below the same old-stage cut.
The key new-generator bound is the genuine S1/S2 numerical-meet cap. -/
theorem compatible_successor_other_below_oldStageTailCut
    {H K : Ordered3Graph Nat} {F f g : Nat → Nat} {m u : Nat}
    (hm : IsLeaf H m)
    (Q : ReservedDiaryStage H K F (m + 1) g)
    (hCompat : CofinalDiaryStageCompatible H m f g)
    (hu : u ∈ countableDiaryFiniteSupport H (m + 1))
    (hum : u ≠ m) :
    g u < oldStageTailCut H m f := by
  classical
  change g u <
    max ((countableDiaryFiniteSupport H m).sup f)
        ((countableDiaryLeafPrefix H m).sup f) + 1
  by_cases huOld : u ∈ countableDiaryFiniteSupport H m
  · calc
      g u = f u := hCompat u huOld
      _ ≤ (countableDiaryFiniteSupport H m).sup f :=
        Finset.le_sup (f := f) huOld
      _ ≤ max ((countableDiaryFiniteSupport H m).sup f)
          ((countableDiaryLeafPrefix H m).sup f) :=
        le_max_left _ _
      _ < max ((countableDiaryFiniteSupport H m).sup f)
          ((countableDiaryLeafPrefix H m).sup f) + 1 :=
        Nat.lt_succ_self _
  · have huNew : u ∈ newNonleafGeneratorSupport H m :=
      (mem_newNonleafGeneratorSupport_iff H m u).mpr
        ⟨hu,huOld,hum⟩
    have hKeep : ∀ a : Nat,
        a ∈ countableDiaryLeafPrefix H m → g a = f a := by
      intro a ha
      exact hCompat a
        (mem_finiteLeafMeetSupport_leaf H
          (countableDiaryLeafPrefix H m) a ha)
    have hBound : g u ≤ (countableDiaryLeafPrefix H m).sup f :=
      new_nonleaf_generator_image_le_old_leaf_sup
        hm Q.1 hKeep huNew
    exact lt_of_le_of_lt
      (hBound.trans (le_max_right _ _))
      (Nat.lt_succ_self _)

/-- Tail replacement can use one cut chosen from f, uniformly for
all compatible successors, not a cut recomputed from each g₀. -/
theorem ReservedDiaryStage.replace_new_leaf_of_old_stage_type
    {H K : Ordered3Graph Nat} {F f g₀ : Nat → Nat}
    {m v : Nat}
    (hm : IsLeaf H m)
    (P : ReservedDiaryStage H K F (m + 1) g₀)
    (hCompat : CofinalDiaryStageCompatible H m f g₀)
    (hType : K.SameOneTypeBelow
      (oldStageTailCut H m f) (g₀ m) v)
    (hvLater : g₀ m ≤ v)
    (hvLeaf : IsLeaf K v)
    (hvRange : ∃ t : Nat, v = F t) :
    ReservedDiaryStage H K F (m + 1)
      (replaceAt g₀ m v) := by
  apply ReservedDiaryStage.replace_new_leaf_of_same_tail_type
    hm P ?_ hType hvLater hvLeaf hvRange
  intro u hu hum
  exact compatible_successor_other_below_oldStageTailCut
    hm P hCompat hu hum

/-- A finitely persistent old stage admits ONE complete nonleaf
generator profile AND ONE complete finite mixed singleton colour
which are jointly realized at EVERY finite horizon.

Different horizons may require different images of the new leaf.
The theorem is deliberately weaker than a persistent successor. -/
theorem persistent_stage_has_stable_profile_and_old_stage_colour
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (hm : IsLeaf H m)
    (P : PersistentReservedDiaryStage H K F m f) :
    ∃ p : ({u : Nat // u ∈ newNonleafGeneratorSupport H m} → Nat),
      ∃ c : Fin (oldStageTailCut H m f) →
          Fin (oldStageTailCut H m f) → Bool,
        ∀ n : Nat, ∃ g : Nat → Nat,
          ReservedDiaryStage H K F (m + 1 + n) g ∧
          CofinalDiaryStageCompatible H m f g ∧
          (∀ u : {u : Nat // u ∈ newNonleafGeneratorSupport H m},
            g u.val = p u) ∧
          DiaryLowerBoundColors.singletonColour K
            (oldStageTailCut H m f) (g m) = c := by
  classical
  obtain ⟨p,hProfiles⟩ :=
    persistent_stage_has_stable_new_nonleaf_record hm P
  let B := oldStageTailCut H m f
  let C := Fin B → Fin B → Bool
  let R : C → Nat → Prop := fun c n =>
    ∃ g : Nat → Nat,
      ReservedDiaryStage H K F (m + 1 + n) g ∧
      CofinalDiaryStageCompatible H m f g ∧
      (∀ u : {u : Nat // u ∈ newNonleafGeneratorSupport H m},
        g u.val = p u) ∧
      DiaryLowerBoundColors.singletonColour K B (g m) = c
  have hDown : ∀ (c : C) (n k : Nat),
      k ≤ n → R c n → R c k := by
    intro c n k hkn
    rintro ⟨g,Q,hOld,hProfile,hColour⟩
    exact ⟨g,Q.restrict (by omega),hOld,hProfile,hColour⟩
  have hCover : ∀ n : Nat, ∃ c : C,
      c ∈ (Finset.univ : Finset C) ∧ R c n := by
    intro n
    obtain ⟨g,Q,hOld,hProfile⟩ := hProfiles n
    let c : C := DiaryLowerBoundColors.singletonColour K B (g m)
    exact ⟨c,Finset.mem_univ _,g,Q,hOld,hProfile,rfl⟩
  obtain ⟨c,_hc,hAll⟩ :=
    finite_choice_persistent_of_downward_type
      (Finset.univ : Finset C) R hDown hCover
  exact ⟨p,c,hAll⟩

end DiaryLeafPriority
end ThreeUniformDiaries
