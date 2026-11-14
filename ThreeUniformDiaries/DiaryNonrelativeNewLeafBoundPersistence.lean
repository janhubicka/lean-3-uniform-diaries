import ThreeUniformDiaries.DiaryCofinalOldBoundPersistenceDichotomy

/-!
# Track D: a persistent next stage iff the unassigned next leaf stays bounded

Apply the checked old-support/last-leaf compactness theorem at source
horizon m+1, where m is a genuine SOURCE leaf and therefore exactly
the LAST selected source leaf.

A complete genuinely reserved next stage on S_(m+1) is FINITELY
PERSISTENT for SOME choice of old map (none is preassigned) iff the
image of that single new leaf m is bounded on cofinally many
independently realized future source horizons.

Its exact negation forces ALL genuine future reserved stage witnesses
to send m beyond every fixed target cutoff at a sufficiently late
source horizon. For true full diaries this escape is nonvacuous:
finite-horizon reserved stages exist independently at every stage.

The existential choice of the entire old map is essential. This
does not assert that a persistent successor exists for an ARBITRARY
previously fixed old map f, or supply a certified countable branch.
The latter relative issue is the still-open Track D critical path.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- For a genuine new source leaf m, the LAST selected source
leaf at horizon m+1 is exactly m itself. -/
theorem max_selected_leaf_at_true_successor
    (H : Ordered3Graph Nat) (m : Nat) (hm : IsLeaf H m) :
    ∃ hNonempty : (countableDiaryLeafPrefix H (m + 1)).Nonempty,
      (countableDiaryLeafPrefix H (m + 1)).max' hNonempty = m := by
  classical
  let L := countableDiaryLeafPrefix H (m + 1)
  have hmMem : m ∈ L :=
    (mem_countableDiaryLeafPrefix_iff H (m + 1) m).mpr
      ⟨hm.1, Nat.lt_succ_self m, hm⟩
  let hNonempty : L.Nonempty := ⟨m, hmMem⟩
  refine ⟨hNonempty, ?_⟩
  apply Nat.le_antisymm
  · have hb : L.max' hNonempty ∈ L := Finset.max'_mem L hNonempty
    have hlt : L.max' hNonempty < m + 1 :=
      ((mem_countableDiaryLeafPrefix_iff H (m + 1)
        (L.max' hNonempty)).mp hb).2.1
    omega
  · exact Finset.le_max' L m hmMem

/-- Without fixing ANY old reserved support f beforehand, some
complete new-stage S_(m+1) map is finitely persistent IFF one
numerical bound controls the new leaf image g(m) at cofinally
many genuine reserved later source horizons.

This is a direct sharp application of old-support finite vector
compactness: m is the LAST source leaf selected at horizon m+1,
so a bound on g(m) automatically bounds every earlier selected
leaf and hence the whole generated finite old+new support. -/
theorem persistentNextStage_iff_cofinalBoundedNewLeafImage
    (H K : Ordered3Graph Nat) (F : Nat → Nat)
    (m : Nat) (hm : IsLeaf H m) :
    (∃ g : Nat → Nat,
      PersistentReservedDiaryStage H K F (m + 1) g) ↔
    (∃ B : Nat, ∀ N : Nat,
      ∃ n : Nat, N ≤ n ∧
        ∃ g : Nat → Nat,
          ReservedDiaryStage H K F (m + 1 + n) g ∧
          g m ≤ B) := by
  obtain ⟨hNonempty, hLast⟩ :=
    max_selected_leaf_at_true_successor H m hm
  simpa only [hLast] using
    (persistentOldSupport_iff_cofinalBoundedLastOldLeaf
      H K F (m + 1) hNonempty)

/-- Exact negation: no complete finitely persistent S_(m+1)
stage exists (even after choosing its OLD map freely) iff for
every target cutoff B there is a finite source horizon N such
that ALL later genuine complete reserved witnesses satisfy
g(m)>B.

The escape branch may be vacuous for arbitrary graphs; the
next genuine full-diary theorem makes it nonvacuous. -/
theorem noPersistentNextStage_iff_eventualNewLeafEscape
    (H K : Ordered3Graph Nat) (F : Nat → Nat)
    (m : Nat) (hm : IsLeaf H m) :
    (¬ ∃ g : Nat → Nat,
      PersistentReservedDiaryStage H K F (m + 1) g) ↔
    (∀ B : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
      ∀ g : Nat → Nat,
        ReservedDiaryStage H K F (m + 1 + n) g →
        B < g m) := by
  obtain ⟨hNonempty, hLast⟩ :=
    max_selected_leaf_at_true_successor H m hm
  simpa only [hLast] using
    (noPersistentOldSupport_iff_eventualLastOldLeafEscape
      H K F (m + 1) hNonempty)

/-- In the original arbitrary unordered induced GENERIC leaf
range of a full RoleDiary, either SOME complete next source stage
S_(m+1) is finitely persistent (with its old f selected freely)
or every sufficiently late horizon FORCES the new leaf image
above any B, while STILL having an actual complete reserved
horizon witness.

This does not give persistent extension of any prescribed old f;
the selected next-stage map may use an unrelated old support. -/
theorem RoleDiary.persistent_next_stage_or_nonvacuous_new_leaf_escape
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (m : Nat) (hm : IsLeaf H m) :
    (∃ g : Nat → Nat,
      PersistentReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g) ∨
    (∀ B : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n →
      (∃ g : Nat → Nat,
        ReservedDiaryStage H K (fun t : Nat => F t) (m + 1 + n) g) ∧
      (∀ g : Nat → Nat,
        ReservedDiaryStage H K (fun t : Nat => F t) (m + 1 + n) g →
        B < g m)) := by
  classical
  by_cases hPersistent :
      ∃ g : Nat → Nat,
        PersistentReservedDiaryStage H K (fun t : Nat => F t) (m + 1) g
  · exact Or.inl hPersistent
  · right
    have hEscape :=
      (noPersistentNextStage_iff_eventualNewLeafEscape
        H K (fun t : Nat => F t) m hm).mp hPersistent
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
    intro B
    obtain ⟨N, hTail⟩ := hEscape B
    refine ⟨N, ?_⟩
    intro n hn
    constructor
    · exact exists_independent_reserved_stage_in_universal_leaf_range
        DH DK G hUniversal F hFLeaf (m + 1 + n)
    · exact hTail n hn

end DiaryLeafPriority
end ThreeUniformDiaries
