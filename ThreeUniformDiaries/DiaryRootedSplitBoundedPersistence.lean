import ThreeUniformDiaries.DiaryPersistentSuccessorBoundEquivalence

/-!
# Track A: exact ROOTED split compactness for persistent reserved next leaves

A numerical next-leaf image bound at cofinally many actual reserved
future SOURCE horizons is precisely what gives a finitely persistent
next stage. If one needs a persistent new image in one SPECIFIED
target one-meet fibre, the finite-choice palette must explicitly
RESTRICT images to that exact split.

This result proves such a *split-specific* iff using only genuine
complete reserved finite diary stages and literal old support
compatibility. No genericity or full RoleDiary hypothesis is used.

CRITICAL: the high-favourable-root and deep reserved immediate
successor theorems do NOT provide the bounded later-HORIZON premise
here. Cofinal target height of immediate successors is not a
replacement for bounded choice through later source horizons.
No unconditional countable diary unavoidability is claimed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- One old-support-compatible, FINITELY PERSISTENT next-leaf
stage whose new leaf has exact target rooted singleton meet s with
a given target root w exists IFF actual later reserved source
horizons over that SAME old support have a uniform finite upper
bound on their new leaf image while retaining the SAME exact
rooted meet s.

The bound is fixed before all source horizons; the high-horizon
witnesses may vary. This is stronger than applying unrestricted
persistentSuccessor_iff_cofinalBoundedNextLeafImages, because the
resulting persistent image must REMAIN in the specified rooted fibre.

No target genericity, RoleDiary, or favourable split is assumed;
the result is a genuine finite-choice / generated-support lemma. -/
theorem persistentReservedNextLeafInRootSplit_iff_cofinallyBoundedRootSplitImages
    {H K : Ordered3Graph Nat} {F f : Nat → Nat}
    {m w s : Nat} (hm : IsLeaf H m) :
    (∃ g : Nat → Nat,
      PersistentReservedDiaryStage H K F (m + 1) g ∧
      CofinalDiaryStageCompatible H m f g ∧
      K.oneMeetLevel w (g m) = s) ↔
    (∃ B : Nat, ∀ N : Nat,
      ∃ n : Nat, N ≤ n ∧
        ∃ g : Nat → Nat,
          ReservedDiaryStage H K F (m + 1 + n) g ∧
          CofinalDiaryStageCompatible H m f g ∧
          g m ≤ B ∧
          K.oneMeetLevel w (g m) = s) := by
  classical
  constructor
  · rintro ⟨g₀, P₀, hOld₀, hSplit₀⟩
    refine ⟨g₀ m, ?_⟩
    intro N
    obtain ⟨gN, QN, hCompat⟩ := P₀.2 N
    have hOldN : CofinalDiaryStageCompatible H m f gN :=
      CofinalDiaryStageCompatible.trans (Nat.le_succ m)
        hOld₀ hCompat
    have hmSelected :
        m ∈ countableDiaryLeafPrefix H (m + 1) :=
      (mem_countableDiaryLeafPrefix_iff H (m + 1) m).mpr
        ⟨hm.1, by omega, hm⟩
    have hmSupported :
        m ∈ countableDiaryFiniteSupport H (m + 1) :=
      mem_finiteLeafMeetSupport_leaf H
        (countableDiaryLeafPrefix H (m + 1)) m hmSelected
    have hSame : gN m = g₀ m := hCompat m hmSupported
    refine ⟨N, le_rfl, gN, QN, hOldN, ?_, ?_⟩
    · exact le_of_eq hSame
    · rw [hSame]
      exact hSplit₀
  · rintro ⟨B, hAll⟩
    let W : Finset Nat :=
      (Finset.range (B + 1)).filter
        (fun v => K.oneMeetLevel w v = s)
    let R : Nat → Nat → Prop := fun v n =>
      ∃ g : Nat → Nat,
        ReservedDiaryStage H K F (m + 1 + n) g ∧
        CofinalDiaryStageCompatible H m f g ∧
        g m = v
    have hDown : ∀ v n k : Nat,
        k ≤ n → R v n → R v k := by
      intro v n k hkn
      rintro ⟨g, Q, hOld, hValue⟩
      exact ⟨g, Q.restrict (by omega), hOld, hValue⟩
    have hCover : ∀ n : Nat,
        ∃ v : Nat, v ∈ W ∧ R v n := by
      intro n
      obtain ⟨q, hNq, g, Q, hOld, hBound, hMeet⟩ := hAll n
      have Qn : ReservedDiaryStage H K F (m + 1 + n) g :=
        Q.restrict (by omega)
      have hIn : g m ∈ W := by
        change g m ∈ (Finset.range (B + 1)).filter
          (fun v => K.oneMeetLevel w v = s)
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (by omega), hMeet⟩
      exact ⟨g m, hIn, g, Qn, hOld, rfl⟩
    obtain ⟨v, hv, hStable⟩ :=
      finite_choice_persistent_of_downward W R hDown hCover
    obtain ⟨g₀, Q₀, hOld₀, hValue₀⟩ := hStable 0
    have Q₀Immediate : ReservedDiaryStage H K F (m + 1) g₀ := by
      simpa only [Nat.add_zero] using Q₀
    have hPersistent : PersistentReservedDiaryStage H K F
        (m + 1) g₀ := by
      refine ⟨Q₀Immediate, ?_⟩
      intro n
      obtain ⟨gN, QN, hOldN, hValueN⟩ := hStable n
      have QNImmediate : ReservedDiaryStage H K F
          (m + 1) gN :=
        QN.restrict (by omega)
      have hSelectedAgreement : ∀ u : Nat,
          u ∈ countableDiaryLeafPrefix H (m + 1) →
            g₀ u = gN u := by
        intro u hu
        rw [countableDiaryLeafPrefix_succ_of_leaf H m hm] at hu
        rcases Finset.mem_insert.mp hu with hUm | hOldLeaf
        · subst u
          exact hValue₀.trans hValueN.symm
        · have huOld : u ∈ countableDiaryFiniteSupport H m :=
            mem_finiteLeafMeetSupport_leaf H
              (countableDiaryLeafPrefix H m) u hOldLeaf
          exact (hOld₀ u huOld).trans (hOldN u huOld).symm
      have hSupportAgreement :=
        Q₀Immediate.1.eq_on_support_of_selected_leaves
          QNImmediate.1 hSelectedAgreement
      refine ⟨gN, QN, ?_⟩
      intro u hu
      exact (hSupportAgreement u hu).symm
    have hvSplit : K.oneMeetLevel w v = s := by
      have hvW : v ∈
          (Finset.range (B + 1)).filter
            (fun z => K.oneMeetLevel w z = s) := hv
      exact (Finset.mem_filter.mp hvW).2
    have hAtSplit : K.oneMeetLevel w (g₀ m) = s := by
      rw [hValue₀]
      exact hvSplit
    exact ⟨g₀, hPersistent, hOld₀, hAtSplit⟩

end DiaryLeafPriority
end ThreeUniformDiaries
