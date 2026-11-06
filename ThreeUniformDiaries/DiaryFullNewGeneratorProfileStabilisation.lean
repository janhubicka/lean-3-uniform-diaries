import ThreeUniformDiaries.DiaryNewNonleafGeneratorImageBound
import ThreeUniformDiaries.DiaryFiniteCandidatePersistentFusion

/-!
# Stabilizing the COMPLETE new nonleaf-generator image record

For a finitely persistent old diary stage and a newly selected leaf m,
arbitrarily long finite reserved extensions preserving the old support
may send the new target leaf to unbounded positions. Nevertheless ALL
new support vertices other than m are capped by previously fixed old
leaf images: the exact finite image-cover theorem supplies a finite
set W of possible FULL new-nonleaf-generator image records.

A general finite-choice compactness lemma makes one record persist at
every finite horizon; no uniform bound on the image of m is used.

This proves a genuine simultaneous split-profile stabilization, not
a finitely persistent new leaf image. The remaining obstruction is
the target leaf's possible escape to infinity inside a fixed finite
split-generator profile. Nothing here implies countable unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The finite-choice argument works for an arbitrary finite type of
profiles, not merely a finite set of Nat coordinates. -/
theorem finite_choice_persistent_of_downward_type
    {α : Type*} [DecidableEq α]
    (W : Finset α) (P : α → Nat → Prop)
    (hDown : ∀ v n k : Nat, k ≤ n → P v n → P v k)
    (hCover : ∀ n : Nat, ∃ v : α, v ∈ W ∧ P v n) :
    ∃ v : α, v ∈ W ∧ ∀ n : Nat, P v n := by
  classical
  by_contra hNone
  have bad : ∀ v : α, v ∈ W → ∃ n : Nat, ¬ P v n := by
    intro v hv
    by_contra h
    push_neg at h
    exact hNone ⟨v,hv,h⟩
  let badN : α → Nat := fun v =>
    if hv : v ∈ W then Classical.choose (bad v hv) else 0
  have hBadN (v : α) (hv : v ∈ W) : ¬ P v (badN v) := by
    simp only [badN, dif_pos hv]
    exact Classical.choose_spec (bad v hv)
  let N := W.sup badN
  obtain ⟨v,hv,hP⟩ := hCover N
  have hBound : badN v ≤ N := by
    exact Finset.le_sup (f := badN) hv
  exact hBadN v hv (hDown v N (badN v) hBound hP)

/-- For any finitely persistent old stage, there is ONE complete
new NONLEAF generator image record occurring in a compatible
reserved realization at every finite horizon after the new leaf.

A witness for each horizon may choose a DIFFERENT image of m.
The finite record does not include that unbounded leaf image.
-/
theorem persistent_stage_has_stable_new_nonleaf_record
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (hm : IsLeaf H m)
    (P : PersistentReservedDiaryStage H K F m f) :
    ∃ p : ({u : Nat // u ∈ newNonleafGeneratorSupport H m} → Nat),
      ∀ n : Nat, ∃ g : Nat → Nat,
        ReservedDiaryStage H K F (m + 1 + n) g ∧
        CofinalDiaryStageCompatible H m f g ∧
        ∀ u : {u : Nat // u ∈ newNonleafGeneratorSupport H m},
          g u.val = p u := by
  classical
  let T := {u : Nat // u ∈ newNonleafGeneratorSupport H m}
  obtain ⟨W,hAllProfiles⟩ :=
    exists_finite_new_nonleaf_profile_cover
      (H := H) (K := K) (F := F) (f := f) (m := m) hm
  let R : (T → Nat) → Nat → Prop := fun p n =>
    ∃ g : Nat → Nat,
      ReservedDiaryStage H K F (m + 1 + n) g ∧
      CofinalDiaryStageCompatible H m f g ∧
      (fun u : T => g u.val) = p
  have hDown : ∀ (p : T → Nat) (n k : Nat),
      k ≤ n → R p n → R p k := by
    intro p n k hkn
    rintro ⟨g,Q,hOld,hProfile⟩
    exact ⟨g,Q.restrict (by omega),hOld,hProfile⟩
  have hCover : ∀ n : Nat,
      ∃ p : T → Nat, p ∈ W ∧ R p n := by
    intro n
    obtain ⟨g,Q,hOld⟩ := P.2 (n + 1)
    have hEq : m + (n + 1) = m + 1 + n := by omega
    rw [hEq] at Q
    have Qnext : ReservedDiaryStage H K F (m + 1) g :=
      Q.restrict (by omega)
    have hKeep : ∀ a : Nat,
        a ∈ countableDiaryLeafPrefix H m → g a = f a := by
      intro a ha
      have haSupport : a ∈ countableDiaryFiniteSupport H m :=
        mem_finiteLeafMeetSupport_leaf H
          (countableDiaryLeafPrefix H m) a ha
      exact hOld a haSupport
    let p : T → Nat := fun u => g u.val
    have hp : p ∈ W := hAllProfiles g Qnext.1 hKeep
    exact ⟨p,hp,g,Q,hOld,rfl⟩
  obtain ⟨p,_hp,hAll⟩ :=
    finite_choice_persistent_of_downward_type W R hDown hCover
  refine ⟨p,?_⟩
  intro n
  obtain ⟨g,Q,hOld,hEq⟩ := hAll n
  refine ⟨g,Q,hOld,?_⟩
  intro u
  exact congrFun hEq u

end DiaryLeafPriority
end ThreeUniformDiaries
