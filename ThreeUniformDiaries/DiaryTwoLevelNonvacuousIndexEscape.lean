import ThreeUniformDiaries.DiaryOldLastLeafGenericIndexPersistence
import ThreeUniformDiaries.DiaryRelativeFixedOldIndexPersistence
import ThreeUniformDiaries.DiaryIndependentReservedStageExistence

/-!
# Track D: two-level NONVACUOUS escape certificates for relative diary fusion

English-first proof/adversarial audit:
  3-uniform-diaries notes/track_d_two_level_nonvacuous_index_escape_20261115.md

For any full source/target RoleDiaries, an original unordered induced
generic target leaf range F, and any genuine NEW source leaf m with
at least one selected earlier true source leaf b=max L_m, we identify
three exhaustive outcomes:

(A) SOME actual complete old reserved support f and SOME compatible
    complete new reserved stage g are BOTH finitely persistent;
(B) there is NO persistent old support; the SAME canonical LAST old
    source leaf b escapes every bounded original F-index prefix at
    every sufficiently late source horizon, with REAL reserved stages
    still existing at each such horizon;
(C) SOME persistent complete old support f exists, but that particular
    f has NO persistent compatible next-leaf successor: the genuine
    new source leaf m escapes every finite original F-index prefix
    uniformly among ALL old-f-compatible stages at sufficiently late
    horizons, with REAL old-f-compatible witnesses at each horizon.

This is an exhaustive disjunction, not a claim that (A) holds.
(A) and (C) can coexist for DIFFERENT old f; the source maps are
not selected to force success. The original F need not preserve
target numerical order.

Proof uses ONLY checked old-support original-index escape iff, fixed-f
relative new-leaf original-index escape iff, and unconditional
independent finite reserved-stage existence. It is not a geometric
argument ruling out either obstruction, not a countable coherent
diary embedding and not the printed unavoidability theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A fully explicit two-level diagnosis of the failure of
relative countable-diary successor fusion, with *genuine*
nonvacuous stage witnesses in BOTH escape alternatives.

Let b=max L_m, where L_m is the nonempty set of EARLIER selected
source leaves. Then EITHER:
1. some persistent old f has a persistent immediate successor
   compatible on the ENTIRE real S1/S2 old support;
2. b eventually avoids every finite prefix F[0,T) along ALL
   actual reserved later horizons, each of which is nonempty;
3. one actual persistent old f has its NEW leaf m eventually
   avoiding every prefix F[0,T) along ALL f-compatible later
   reserved stages, with one such stage existing at each horizon.

The old f in (3) is selected BEFORE T,N and all witnesses. The
disjunction is not pairwise exclusive between (1) and (3).
The theorem assumes actual full RoleDiaries; it does not assert
that either escape alternative can be ruled out. -/
theorem RoleDiary.persistent_relative_pair_or_nonvacuous_two_level_index_escape
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (m : Nat) (hm : IsLeaf H m)
    (hOld : (countableDiaryLeafPrefix H m).Nonempty) :
    (∃ f : Nat → Nat,
      PersistentReservedDiaryStage H K (fun t : Nat => F t) m f ∧
      ∃ g : Nat → Nat,
        PersistentReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g ∧
        CofinalDiaryStageCompatible H m f g) ∨
    (∀ T : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
      (∃ g : Nat → Nat,
        ReservedDiaryStage H K (fun t : Nat => F t) (m + n) g) ∧
      (∀ g : Nat → Nat,
        ReservedDiaryStage H K (fun t : Nat => F t) (m + n) g →
        ∀ t : Nat, t < T →
          g ((countableDiaryLeafPrefix H m).max' hOld) ≠ F t)) ∨
    (∃ f : Nat → Nat,
      PersistentReservedDiaryStage H K (fun t : Nat => F t) m f ∧
      ∀ T : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
        (∃ g : Nat → Nat,
          ReservedDiaryStage H K (fun t : Nat => F t) (m + 1 + n) g ∧
          CofinalDiaryStageCompatible H m f g) ∧
        (∀ g : Nat → Nat,
          ReservedDiaryStage H K (fun t : Nat => F t) (m + 1 + n) g →
          CofinalDiaryStageCompatible H m f g →
          ∀ t : Nat, t < T → g m ≠ F t)) := by
  classical
  by_cases hPersistent :
      ∃ f : Nat → Nat,
        PersistentReservedDiaryStage H K (fun t : Nat => F t) m f
  · obtain ⟨f, Pf⟩ := hPersistent
    by_cases hNext :
        ∃ g : Nat → Nat,
          PersistentReservedDiaryStage H K
            (fun t : Nat => F t) (m + 1) g ∧
          CofinalDiaryStageCompatible H m f g
    · exact Or.inl ⟨f, Pf, hNext⟩
    · right
      right
      have hIndexEscape :
          EventuallyEscapingNextLeafRangeIndices
            H K (fun t : Nat => F t) f m :=
        (noPersistentRelativeSuccessor_iff_eventualNewLeafIndexEscape
          (H := H) (K := K) (F := fun t : Nat => F t)
          (f := f) (m := m) hm).mp hNext
      refine ⟨f, Pf, ?_⟩
      intro T
      obtain ⟨N, hTail⟩ := hIndexEscape T
      refine ⟨N, ?_⟩
      intro n hn
      constructor
      · obtain ⟨g, Q, hOldKeep⟩ := Pf.2 (n + 1)
        have hEq : m + (n + 1) = m + 1 + n := by omega
        exact ⟨g, by simpa only [hEq] using Q, hOldKeep⟩
      · exact hTail n hn
  · right
    left
    have hIndexEscape :=
      (noPersistentOldSupport_iff_eventualLastOldLeafIndexEscape
        H K (fun t : Nat => F t) m hOld).mp hPersistent
    have hUniversal : Ordered3Graph.CountablyUniversal G.graph := by
      intro A
      obtain ⟨v, hMono, hInduced⟩ :=
        G.exists_countable_induced_embedding A
      let e : Ordered3Graph.Embedding A G.graph := {
        toFun := v
        strictMono := hMono
        edge_iff := by
          intro a b c hab hbc
          exact hInduced a b c hab hbc
      }
      exact ⟨e.asUnordered⟩
    intro T
    obtain ⟨N, hTail⟩ := hIndexEscape T
    refine ⟨N, ?_⟩
    intro n hn
    constructor
    · exact exists_independent_reserved_stage_in_universal_leaf_range
        DH DK G hUniversal F hFLeaf (m + n)
    · exact hTail n hn

end DiaryLeafPriority
end ThreeUniformDiaries
