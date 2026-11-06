import ThreeUniformDiaries.DiaryFullNewGeneratorProfileStabilisation
import ThreeUniformDiaries.DiaryPersistentLeafEscapeDichotomy

/-!
# Escaping target leaf images within ONE stabilized split-generator record

For any finitely persistent old diary stage and genuine next leaf m,
the finite capped-meet argument gives one complete new nonleaf
generator profile that appears at arbitrarily large finite horizons.

If there is NO finitely persistent successor fixing the old support,
the previously verified escape dichotomy forces ALL compatible
next-leaf images to exceed any prescribed bound at some horizon.
In particular this happens even after fixing the one split record
that recurs at EVERY finite horizon.

This is a precise conditional obstruction, not a proof that the
escape alternative is impossible in a genuine full diary. It does
not produce a countable source diary embedding.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- If no fixed next target leaf image is finitely persistent,
there is a single, uniformly bounded NEW NONLEAF generator profile
with compatible realizations at every finite horizon, but for every
B there is a horizon at which all compatible realizations, including
those with this fixed profile, send the next leaf above B.

The conclusion is therefore a genuinely nonvacuous escape in one
stabilized finite split cone, not a varying split-profile artifact. -/
theorem fixed_new_nonleaf_profile_has_unbounded_leaf_escape
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (hm : IsLeaf H m)
    (P : PersistentReservedDiaryStage H K F m f)
    (hNo : ¬ ∃ g : Nat → Nat,
      PersistentReservedDiaryStage H K F (m + 1) g ∧
      CofinalDiaryStageCompatible H m f g) :
    ∃ p : ({u : Nat // u ∈ newNonleafGeneratorSupport H m} → Nat),
      (∀ n : Nat, ∃ g : Nat → Nat,
        ReservedDiaryStage H K F (m + 1 + n) g ∧
        CofinalDiaryStageCompatible H m f g ∧
        ∀ u : {u : Nat // u ∈ newNonleafGeneratorSupport H m},
          g u.val = p u) ∧
      (∀ B : Nat, ∃ n : Nat,
        (∃ g : Nat → Nat,
          ReservedDiaryStage H K F (m + 1 + n) g ∧
          CofinalDiaryStageCompatible H m f g ∧
          ∀ u : {u : Nat // u ∈ newNonleafGeneratorSupport H m},
            g u.val = p u) ∧
        ∀ g : Nat → Nat,
          ReservedDiaryStage H K F (m + 1 + n) g →
          CofinalDiaryStageCompatible H m f g →
          B < g m) := by
  obtain ⟨p,hStableProfile⟩ :=
    persistent_stage_has_stable_new_nonleaf_record hm P
  have hEsc :
      ∀ B : Nat, ∃ n : Nat,
        (∃ g : Nat → Nat,
          ReservedDiaryStage H K F (m + 1 + n) g ∧
          CofinalDiaryStageCompatible H m f g) ∧
        (∀ g : Nat → Nat,
          ReservedDiaryStage H K F (m + 1 + n) g →
          CofinalDiaryStageCompatible H m f g →
          B < g m) := by
    rcases persistent_next_leaf_or_eventual_escape hm P with hGood | hBad
    · exact False.elim (hNo hGood)
    · exact hBad
  refine ⟨p,hStableProfile,?_⟩
  intro B
  obtain ⟨n,_hSome,hBound⟩ := hEsc B
  obtain ⟨g,Q,hOld,hRecord⟩ := hStableProfile n
  exact ⟨n,⟨g,Q,hOld,hRecord⟩,hBound⟩

end DiaryLeafPriority
end ThreeUniformDiaries
