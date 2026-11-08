import ThreeUniformDiaries.DiaryPersistentUniformEscape
import ThreeUniformDiaries.DiaryFixedProfileUniformBoundCriterion

/-!
# Track C: exact eventual escape in target numbers versus leaf-range indices

An unordered prescribed leaf map F : Nat → Nat has no reason to
preserve target numerical order. Consequently the assertion that
all sufficiently late compatible next-leaf images exceed every
numeric bound is not automatically syntactically the same as
escaping every finite set of F-preimage indices.

For *genuine* reserved stages, every new source leaf image belongs
to F[Nat]. A finite set of small target values has a uniformly
bounded chosen section of F (without injectivity/monotonicity);
conversely the finite F-image of a bounded index set has a
numerical supremum. These finite facts give a genuine iff.

The result compares conditional ESCAPE properties, not existence
of bounded candidates, not absence of escape, and not countable
diary unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Beyond each numerical cutoff B, every sufficiently late
old-compatible reserved realization sends the next source leaf m
to a target vertex greater than B. Nonemptiness is *not* built
into the definition; an old persistent stage supplies it later. -/
def EventuallyNumericallyEscapingNextLeaf
    (H K : Ordered3Graph Nat) (F f : Nat → Nat) (m : Nat) : Prop :=
  ∀ B : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
    ∀ g : Nat → Nat,
      ReservedDiaryStage H K F (m + 1 + n) g →
      CofinalDiaryStageCompatible H m f g →
      B < g m

/-- Beyond each bounded set of input indices t<T, every late
old-compatible reserved realization has next leaf image outside
F[0,T). The map F may be arbitrary: no monotonicity or injectivity. -/
def EventuallyEscapingNextLeafRangeIndices
    (H K : Ordered3Graph Nat) (F f : Nat → Nat) (m : Nat) : Prop :=
  ∀ T : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
    ∀ g : Nat → Nat,
      ReservedDiaryStage H K F (m + 1 + n) g →
      CofinalDiaryStageCompatible H m f g →
      ∀ t : Nat, t < T → g m ≠ F t

/-- For genuine source leaves, eventual numerical target-image
escape iff eventual avoidance of every finite F-preimage prefix.
Every actual new-leaf realization lies in F[Nat] by admissibility.
The equivalence remains valid for an UNORDERED, even noninjective F. -/
theorem eventualNumericEscape_iff_eventualRangeIndexEscape
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (hm : IsLeaf H m) :
    EventuallyNumericallyEscapingNextLeaf H K F f m ↔
      EventuallyEscapingNextLeafRangeIndices H K F f m := by
  classical
  constructor
  · intro hNum T
    let B : Nat := (Finset.range T).sup F
    obtain ⟨N, hAll⟩ := hNum B
    refine ⟨N, ?_⟩
    intro n hn g Q hOld t ht hEq
    have hSmall : F t ≤ B :=
      Finset.le_sup (f := F) (Finset.mem_range.mpr ht)
    have hLarge : B < g m := hAll n hn g Q hOld
    rw [hEq] at hLarge
    omega
  · intro hIndex B
    obtain ⟨T, hSection⟩ :=
      bounded_range_values_have_bounded_preimage_indices F B
    obtain ⟨N, hAll⟩ := hIndex T
    refine ⟨N, ?_⟩
    intro n hn g Q hOld
    by_contra hNot
    have hSmall : g m ≤ B := by omega
    have hmSupported :
        m ∈ countableDiaryFiniteSupport H (m + 1 + n) :=
      mem_finiteLeafMeetSupport_leaf H
        (countableDiaryLeafPrefix H (m + 1 + n)) m
        ((mem_countableDiaryLeafPrefix_iff H (m + 1 + n) m).mpr
          ⟨hm.1, by omega, hm⟩)
    obtain ⟨t, ht⟩ := Q.1.leaf_range m hmSupported hm
    obtain ⟨t', ht', hImage⟩ :=
      hSection (g m) hSmall ⟨t, ht.symm⟩
    exact (hAll n hn g Q hOld t' ht') hImage.symm

/-- The actual old persistence hypothesis supplies a real map
at every finite continuation horizon. The verified global
next-leaf persistence/escape dichotomy can therefore be stated
in terms of unbounded PREIMAGE INDICES in the original arbitrary
prescribed leaf map F, with nonvacuity at every later horizon.

This does not rule out the escape branch. -/
theorem persistentSuccessor_or_eventualRangeIndexEscape
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (hm : IsLeaf H m)
    (P : PersistentReservedDiaryStage H K F m f) :
    (∃ g : Nat → Nat,
      PersistentReservedDiaryStage H K F (m + 1) g ∧
      CofinalDiaryStageCompatible H m f g) ∨
    (∀ T : Nat, ∃ N : Nat,
      ∀ n : Nat, N ≤ n →
        (∃ g : Nat → Nat,
          ReservedDiaryStage H K F (m + 1 + n) g ∧
          CofinalDiaryStageCompatible H m f g) ∧
        (∀ g : Nat → Nat,
          ReservedDiaryStage H K F (m + 1 + n) g →
          CofinalDiaryStageCompatible H m f g →
          ∀ t : Nat, t < T → g m ≠ F t)) := by
  rcases persistent_next_leaf_or_eventual_uniform_escape hm P with
    hSucc | hEscape
  · exact Or.inl hSucc
  · right
    have hNumeric :
        EventuallyNumericallyEscapingNextLeaf H K F f m := by
      intro B
      obtain ⟨N, hAll⟩ := hEscape B
      refine ⟨N, ?_⟩
      intro n hn g Q hOld
      exact (hAll n hn).2 g Q hOld
    have hIndex :
        EventuallyEscapingNextLeafRangeIndices H K F f m :=
      (eventualNumericEscape_iff_eventualRangeIndexEscape hm).mp
        hNumeric
    intro T
    obtain ⟨N, hAll⟩ := hIndex T
    refine ⟨N, ?_⟩
    intro n hn
    constructor
    · obtain ⟨g, Q, hOld⟩ := P.2 (n + 1)
      have hEq : m + (n + 1) = m + 1 + n := by omega
      exact ⟨g, by simpa only [hEq] using Q, hOld⟩
    · exact hAll n hn

end DiaryLeafPriority
end ThreeUniformDiaries
