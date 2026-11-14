import ThreeUniformDiaries.DiaryTwoLevelNonvacuousIndexEscape

/-!
# Track D: exact obstruction to existence of even ONE persistent relative pair

English-first audit: the checked two-level trichotomy is exhaustive
but the positive branch and its "some persistent old f escapes" branch
can coexist when they use DIFFERENT old f.

If there is NO persistent compatible pair at all, the correct
sharpening is a genuine IFF:
 * either ALL finite source stages force escape of the same fixed
   canonical last OLD source leaf b beyond every original F-index
   cutoff, with actual stages still present; or
 * there exists at least one genuine persistent old stage, and
   EVERY persistent old stage f individually forces escape of the
   NEXT source leaf m in all genuinely reserved f-compatible late
   horizons, again with actual compatible stage witnesses present.

The universal quantifier over all persistent f is essential.
Without it the alleged equivalence would be false: some bad old f
can coexist with another f admitting a persistent successor.

All witnesses are in the ORIGINAL unordered induced generic F range.
Neither escape alternative is ruled out by genericity alone.
This is a failure certificate, not countable unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A precise NONVACUOUS iff for failure of all persistent relative
successors at a true source new leaf m having at least one old
selected source leaf b=max L_m.

NO persistent old/next compatible pair exists iff:

(1) for each F-index cutoff T all sufficiently late genuine reserved
old S_(m+n) stages send b outside F[0,T), but actual stages EXIST at
each such horizon; OR

(2) at least one persistent complete old S_m stage exists, but for
EVERY such persistent f and each cutoff T all sufficiently late
actual f-compatible stages at m+1+n send new m outside F[0,T),
while actual f-compatible stages still EXIST at every horizon.

The `∀ f` in (2), not merely `∃ f`, distinguishes a genuine
global local obstruction from a bad choice of f in one branch. -/
theorem RoleDiary.no_persistent_relative_pair_iff_nonvacuous_two_level_index_escape
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (m : Nat) (hm : IsLeaf H m)
    (hOld : (countableDiaryLeafPrefix H m).Nonempty) :
    (¬ ∃ f : Nat → Nat,
      PersistentReservedDiaryStage H K (fun t : Nat => F t) m f ∧
      ∃ g : Nat → Nat,
        PersistentReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g ∧
        CofinalDiaryStageCompatible H m f g) ↔
    ( (∀ T : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
        (∃ g : Nat → Nat,
          ReservedDiaryStage H K (fun t : Nat => F t) (m + n) g) ∧
        (∀ g : Nat → Nat,
          ReservedDiaryStage H K (fun t : Nat => F t) (m + n) g →
          ∀ t : Nat, t < T →
            g ((countableDiaryLeafPrefix H m).max' hOld) ≠ F t)) ∨
      ((∃ f : Nat → Nat,
          PersistentReservedDiaryStage H K (fun t : Nat => F t) m f) ∧
        (∀ f : Nat → Nat,
          PersistentReservedDiaryStage H K (fun t : Nat => F t) m f →
          ∀ T : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
            (∃ g : Nat → Nat,
              ReservedDiaryStage H K (fun t : Nat => F t)
                (m + 1 + n) g ∧
              CofinalDiaryStageCompatible H m f g) ∧
            (∀ g : Nat → Nat,
              ReservedDiaryStage H K (fun t : Nat => F t)
                (m + 1 + n) g →
              CofinalDiaryStageCompatible H m f g →
              ∀ t : Nat, t < T → g m ≠ F t))) := by
  classical
  constructor
  · intro hNoPair
    rcases DH.persistent_relative_pair_or_nonvacuous_two_level_index_escape
      DK G F hFLeaf m hm hOld with hPair | hOldEscape | hNewEscape
    · exact False.elim (hNoPair hPair)
    · exact Or.inl hOldEscape
    · right
      obtain ⟨f₀, Pf₀, _hBad₀⟩ := hNewEscape
      refine ⟨⟨f₀, Pf₀⟩, ?_⟩
      intro f Pf
      have hNoNext :
          ¬ ∃ g : Nat → Nat,
            PersistentReservedDiaryStage H K
              (fun t : Nat => F t) (m + 1) g ∧
            CofinalDiaryStageCompatible H m f g := by
        intro hNext
        exact hNoPair ⟨f, Pf, hNext⟩
      have hIndex :
          EventuallyEscapingNextLeafRangeIndices
            H K (fun t : Nat => F t) f m :=
        (noPersistentRelativeSuccessor_iff_eventualNewLeafIndexEscape
          (H := H) (K := K) (F := fun t : Nat => F t)
          (f := f) (m := m) hm).mp hNoNext
      intro T
      obtain ⟨N, hTail⟩ := hIndex T
      refine ⟨N, ?_⟩
      intro n hn
      constructor
      · obtain ⟨g, Q, hKeep⟩ := Pf.2 (n + 1)
        have hEq : m + (n + 1) = m + 1 + n := by omega
        exact ⟨g, by simpa only [hEq] using Q, hKeep⟩
      · exact hTail n hn
  · intro hObstruction
    intro hPair
    obtain ⟨f, Pf, g, Pg, hCompatible⟩ := hPair
    rcases hObstruction with hOldEscape | ⟨_hPersistentExists, hAllBad⟩
    · have hOldIndexEscape :
          ∀ T : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
            ∀ g : Nat → Nat,
              ReservedDiaryStage H K (fun t : Nat => F t) (m + n) g →
              ∀ t : Nat, t < T →
                g ((countableDiaryLeafPrefix H m).max' hOld) ≠ F t := by
        intro T
        obtain ⟨N, hAll⟩ := hOldEscape T
        exact ⟨N, fun n hn g Q t ht => (hAll n hn).2 g Q t ht⟩
      have hNoOld :
          ¬ ∃ h : Nat → Nat,
            PersistentReservedDiaryStage H K
              (fun t : Nat => F t) m h :=
        (noPersistentOldSupport_iff_eventualLastOldLeafIndexEscape
          H K (fun t : Nat => F t) m hOld).mpr
          hOldIndexEscape
      exact hNoOld ⟨f, Pf⟩
    · have hIndexEscape :
          EventuallyEscapingNextLeafRangeIndices
            H K (fun t : Nat => F t) f m := by
        intro T
        obtain ⟨N, hAll⟩ := hAllBad f Pf T
        exact ⟨N, fun n hn h Q hKeep t ht =>
          (hAll n hn).2 h Q hKeep t ht⟩
      have hNoNext :
          ¬ ∃ h : Nat → Nat,
            PersistentReservedDiaryStage H K
              (fun t : Nat => F t) (m + 1) h ∧
            CofinalDiaryStageCompatible H m f h :=
        (noPersistentRelativeSuccessor_iff_eventualNewLeafIndexEscape
          (H := H) (K := K) (F := fun t : Nat => F t)
          (f := f) (m := m) hm).mpr hIndexEscape
      exact hNoNext ⟨g, Pg, hCompatible⟩

end DiaryLeafPriority
end ThreeUniformDiaries
