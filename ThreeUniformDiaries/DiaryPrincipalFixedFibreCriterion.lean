import ThreeUniformDiaries.DiaryPersistentFiniteColourIsolation

/-!
# Track C: exact principal finite-colour criterion in one relative fixed fibre

English proof and adversarial audit:
  janhubicka/3-uniform-diaries PR #281

For a full target RoleDiary, a persistent successor preserving one fixed
new-generator profile p and one complete old-cut colour c₀ exists IFF an
actual target leaf u has its finitely SELF-ISOLATING mixed singleton colour
at cut u realized cofinally by genuine old-compatible finite stages in the
SAME (p,c₀)-fibre.

The proof uses the already certified fixed-fibre finite-choice theorem
and finite true-leaf isolation. The existence of such u remains the open
geometric critical path. No countable type compactness is assumed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A precisely fixed relative leaf fibre has one persistent next leaf
IFF one genuine target leaf has its ONE finite self-isolating mixed
singleton mask recurrent in genuine arbitrarily long compatible
realizations of THAT SAME generator-profile and old-cut-colour fibre.

The forward direction uses the persistent map's own next leaf and
literal agreement on all generated S_(m+1) support. The converse uses
true-leaf self-cut isolation, finite-stage restriction, and verified
uniform bounded-image finite choice. -/
theorem persistent_jointProfileColour_iff_cofinal_principal_leaf_colour
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (DK : RoleDiary K)
    (hm : IsLeaf H m)
    (p : ({u : Nat // u ∈ newNonleafGeneratorSupport H m} → Nat))
    (c₀ : Fin (oldStageTailCut H m f) →
      Fin (oldStageTailCut H m f) → Bool) :
    HasPersistentNextLeafWithJointProfileColour H K F f m p c₀ ↔
      ∃ u : Nat, IsLeaf K u ∧
        ∀ N : Nat, ∃ n : Nat, N ≤ n ∧
          ∃ g : Nat → Nat,
            ReservedDiaryStage H K F (m + 1 + n) g ∧
            CofinalDiaryStageCompatible H m f g ∧
            (∀ x : {x : Nat // x ∈ newNonleafGeneratorSupport H m},
              g x.val = p x) ∧
            DiaryLowerBoundColors.singletonColour K
              (oldStageTailCut H m f) (g m) = c₀ ∧
            DiaryLowerBoundColors.singletonColour K u (g m) =
              DiaryLowerBoundColors.singletonColour K u u := by
  constructor
  · rintro ⟨g₀, P₀, hOld₀, hProfile₀, hColour₀⟩
    have hmNext : m ∈ countableDiaryFiniteSupport H (m + 1) := by
      exact mem_finiteLeafMeetSupport_leaf H
        (countableDiaryLeafPrefix H (m + 1)) m
        ((mem_countableDiaryLeafPrefix_iff H (m + 1) m).mpr
          ⟨hm.1, by omega, hm⟩)
    have hu : IsLeaf K (g₀ m) :=
      P₀.1.1.leaf_role m hmNext hm
    refine ⟨g₀ m, hu, ?_⟩
    intro N
    obtain ⟨gN, QN, hCompatible⟩ := P₀.2 N
    have hOldN : CofinalDiaryStageCompatible H m f gN := by
      intro x hx
      have hxNext : x ∈ countableDiaryFiniteSupport H (m + 1) :=
        countableDiaryFiniteSupport_mono H m (m + 1) (by omega) hx
      exact (hCompatible x hxNext).trans (hOld₀ x hx)
    have hProfileN :
        ∀ x : {x : Nat // x ∈ newNonleafGeneratorSupport H m},
          gN x.val = p x := by
      intro x
      have hxNext : x.val ∈ countableDiaryFiniteSupport H (m + 1) :=
        ((mem_newNonleafGeneratorSupport_iff H m x.val).mp
          x.property).1
      exact (hCompatible x.val hxNext).trans (hProfile₀ x)
    have hColourN :
        DiaryLowerBoundColors.singletonColour K
          (oldStageTailCut H m f) (gN m) = c₀ := by
      rw [hCompatible m hmNext]
      exact hColour₀
    refine ⟨N, le_rfl, gN, QN, hOldN, hProfileN, hColourN, ?_⟩
    exact congrArg
      (DiaryLowerBoundColors.singletonColour K (g₀ m))
      (hCompatible m hmNext)
  · rintro ⟨u, hu, hRecur⟩
    apply (persistent_jointProfileColour_iff_uniform_nextLeaf_bound
      hm p c₀).mpr
    refine ⟨u, ?_⟩
    intro N
    obtain ⟨n, hn, g, Q, hOld, hProfile, hColour, hPrincipal⟩ :=
      hRecur N
    have hmSelected : m ∈ countableDiaryLeafPrefix H (m + 1 + n) :=
      (mem_countableDiaryLeafPrefix_iff H (m + 1 + n) m).mpr
        ⟨hm.1, by omega, hm⟩
    have hmSupported : m ∈ countableDiaryFiniteSupport H (m + 1 + n) :=
      mem_finiteLeafMeetSupport_leaf H
        (countableDiaryLeafPrefix H (m + 1 + n)) m hmSelected
    have hTargetLeaf : IsLeaf K (g m) :=
      Q.1.leaf_role m hmSupported hm
    have hEq : u = g m :=
      (DK.singletonColour_self_cut_isolates_leaf
        u (g m) hu hTargetLeaf).mp hPrincipal.symm
    have QN : ReservedDiaryStage H K F (m + 1 + N) g :=
      Q.restrict (by omega)
    refine ⟨g, QN, hOld, hProfile, hColour, ?_⟩
    omega

end DiaryLeafPriority
end ThreeUniformDiaries
