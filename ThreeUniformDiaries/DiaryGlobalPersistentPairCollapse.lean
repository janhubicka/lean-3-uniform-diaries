import ThreeUniformDiaries.DiaryNoPersistentPairExactIndexObstruction
import ThreeUniformDiaries.DiaryNonrelativeNewLeafBoundPersistence
import ThreeUniformDiaries.DiaryOldLastLeafGenericIndexPersistence

/-!
# Track D: global persistent relative-pair existence collapses to next-stage existence

The verified two-level old/new index-escape obstruction distinguishes
TWO geometric failure mechanisms. However, for the GLOBAL question
whether ANY persistent compatible old/next pair exists, the old
persistent map is existential and adds no new requirement.

A genuinely finitely persistent reserved map on S_n restricts to a
finitely persistent map on EVERY earlier supported S_m, m<=n: to
realize old horizon m+k, take its actual persistence witness at
n+k, then restrict back to m+k. Literal compatibility descends to
S_m. Both genuine structure and future reserve are preserved.

Thus an existential persistent pair (f at S_m, compatible persistent
g at S_(m+1)) is equivalent to ANY persistent S_(m+1) stage g. In
the converse choose the old map f to be the SAME total map g,
restricted to the old support; compatibility is reflexive.

For a genuine new source leaf in full diaries and an original
unordered induced generic true-leaf target map F, the checked
NONRELATIVE index-escape iff therefore characterizes failure
of ANY persistent relative pair by one eventually escaping new
leaf m in ALL actual reserved later finite stages. The true
full-diary finite-stage theorem makes the escape NONVACUOUS.

This simplifies the GLOBAL failure recognition, but does not
show that a preselected persistent old f has a successor, or
prove a coherent countable diary embedding/unavoidability.
The earlier two-level trichotomy remains a diagnostic split,
not the logically simplest criterion for global pair existence.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Persistent complete reserved stage maps literally restrict to
earlier canonical finite S1/S2 supports. Finite persistence is
inherited: witness n+k restricts to m+k without changing images.
No infinite branch or geometric genericity is needed. -/
theorem PersistentReservedDiaryStage.restrict_to_earlier
    {H K : Ordered3Graph Nat} {F f : Nat → Nat}
    {m n : Nat}
    (P : PersistentReservedDiaryStage H K F n f)
    (hmn : m ≤ n) :
    PersistentReservedDiaryStage H K F m f := by
  refine ⟨P.1.restrict hmn, ?_⟩
  intro k
  obtain ⟨g, Q, hKeep⟩ := P.2 k
  refine ⟨g, Q.restrict (by omega), ?_⟩
  exact CofinalDiaryStageCompatible.restrict hmn hKeep

/-- Existential persistent old/next pair iff ANY persistent next
stage exists. The reverse direction selects f=g as TOTAL maps,
but interprets f only on S_m, where g has a certified persistent
restriction. The full old support compatibility is literally
reflexive; there is no choice of a previously prescribed f.

This holds for arbitrary H,K,F and m, without IsLeaf or RoleDiary. -/
theorem persistent_relative_pair_iff_persistent_next_stage
    (H K : Ordered3Graph Nat) (F : Nat → Nat) (m : Nat) :
    (∃ f : Nat → Nat,
      PersistentReservedDiaryStage H K F m f ∧
      ∃ g : Nat → Nat,
        PersistentReservedDiaryStage H K F (m + 1) g ∧
        CofinalDiaryStageCompatible H m f g) ↔
      (∃ g : Nat → Nat,
        PersistentReservedDiaryStage H K F (m + 1) g) := by
  constructor
  · rintro ⟨_f, _Pf, g, Pg, _hOld⟩
    exact ⟨g, Pg⟩
  · rintro ⟨g, Pg⟩
    exact ⟨g, Pg.restrict_to_earlier (Nat.le_succ m),
      g, Pg, CofinalDiaryStageCompatible.refl g m⟩

/-- Direct positive GLOBAL pair criterion in the original prescribed
F-preimage indices. At a genuine new source leaf m, existence of
SOME persistent old/next compatible pair is equivalent to ONE
finite original F-index prefix containing actual new-leaf images in
cofinally late genuine reserved future stages.

The old f is NOT fixed in advance. Persistent finite-support
compactness selects it from the bounded new images. The criterion
does not imply relative successor extension for a SPECIFIED f. -/
theorem persistent_relative_pair_iff_cofinalBoundedNewLeafIndex
    (H K : Ordered3Graph Nat) (F : Nat → Nat)
    (m : Nat) (hm : IsLeaf H m) :
    (∃ f : Nat → Nat,
      PersistentReservedDiaryStage H K F m f ∧
      ∃ g : Nat → Nat,
        PersistentReservedDiaryStage H K F (m + 1) g ∧
        CofinalDiaryStageCompatible H m f g) ↔
    (∃ T : Nat, ∀ N : Nat,
      ∃ n : Nat, N ≤ n ∧
        ∃ g : Nat → Nat,
          ReservedDiaryStage H K F (m + 1 + n) g ∧
          ∃ t : Nat, t < T ∧ g m = F t) := by
  exact (persistent_relative_pair_iff_persistent_next_stage H K F m).trans
    (persistentNextStage_iff_cofinalBoundedNewLeafIndex H K F m hm)

/-- Exact NONVACUOUS global failure recognition in a genuine
full diary with original UNORDERED induced generic true-leaf F.

There is NO pair of literal compatible persistent old/next-stage
maps at source m,m+1 IFF every bounded original generic F-index
prefix is eventually avoided by the new source leaf m in ALL
genuine reserved later source stages, while every such horizon
has an ACTUAL reserved stage witness.

Unlike the two-level diagnostic theorem, no source old-leaf
nonemptiness hypothesis is needed. This also covers the first
source leaf. The statement does NOT say all old f extend, or
rule out the escape branch. -/
theorem RoleDiary.no_persistent_pair_iff_nonvacuous_global_next_index_escape
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (m : Nat) (hm : IsLeaf H m) :
    (¬ ∃ f : Nat → Nat,
      PersistentReservedDiaryStage H K (fun t : Nat => F t) m f ∧
      ∃ g : Nat → Nat,
        PersistentReservedDiaryStage H K (fun t : Nat => F t)
          (m + 1) g ∧
        CofinalDiaryStageCompatible H m f g) ↔
    (∀ T : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
      (∃ g : Nat → Nat,
        ReservedDiaryStage H K (fun t : Nat => F t)
          (m + 1 + n) g) ∧
      (∀ g : Nat → Nat,
        ReservedDiaryStage H K (fun t : Nat => F t)
          (m + 1 + n) g →
        ∀ t : Nat, t < T → g m ≠ F t)) := by
  classical
  have hIff :=
    persistent_relative_pair_iff_persistent_next_stage
      H K (fun t : Nat => F t) m
  have hIndex :=
    noPersistentNextStage_iff_eventualNewLeafIndexEscape
      H K (fun t : Nat => F t) m hm
  constructor
  · intro hNoPair
    have hNoNext :
        ¬ ∃ g : Nat → Nat,
          PersistentReservedDiaryStage H K
            (fun t : Nat => F t) (m + 1) g := by
      intro hNext
      exact hNoPair (hIff.mpr hNext)
    have hEscape := hIndex.mp hNoNext
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
    obtain ⟨N, hAll⟩ := hEscape T
    refine ⟨N, ?_⟩
    intro n hn
    constructor
    · exact exists_independent_reserved_stage_in_universal_leaf_range
        DH DK G hUniversal F hFLeaf (m + 1 + n)
    · exact hAll n hn
  · intro hNonvacuous hPair
    have hEsc :
        ∀ T : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
          ∀ g : Nat → Nat,
            ReservedDiaryStage H K (fun t : Nat => F t)
              (m + 1 + n) g →
            ∀ t : Nat, t < T → g m ≠ F t := by
      intro T
      obtain ⟨N, hAll⟩ := hNonvacuous T
      exact ⟨N, fun n hn g Q t ht =>
        (hAll n hn).2 g Q t ht⟩
    exact (hIndex.mpr hEsc) (hIff.mp hPair)

end DiaryLeafPriority
end ThreeUniformDiaries
