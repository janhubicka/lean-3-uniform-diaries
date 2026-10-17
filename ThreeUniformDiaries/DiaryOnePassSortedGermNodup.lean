import ThreeUniformDiaries.DiaryOnePassSelectedEventRealization

/-!
# Sorting actual one-pass singleton germs never duplicates an event

The static one-pass schedule orders the selected realised singleton
children by descending finite binary word rank. For a genuine fresh
V1 witness at event class g, we need to know the selected class g
appears at EXACTLY one position in that list. Mere preservation of
membership and length was not enough: the absence of duplicates is
a separate finite-list invariant.

Prove descending insertion preserves Nodup when the inserted germ
was absent, then sorting preserves Nodup. In particular the sorted
list obtained from an actual Finset of selected children contains
each selected class exactly once.

No S1/S2 or target diary axiom is involved. The labelled event
index uniqueness proof will combine this with the pair/singleton
map and concatenation in the concrete block scheduler.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A descending-rank insertion preserves a duplicate-free
list if the inserted original germ is new. -/
theorem insertOneGermDescending_nodup
    (m : Nat) (g : OneGermSpace m)
    (children : List (OneGermSpace m))
    (hne : g ∉ children)
    (hnodup : children.Nodup) :
    (insertOneGermDescending m g children).Nodup := by
  induction children with
  | nil =>
    simp [insertOneGermDescending]
  | cons h tail ih =>
    have hgNe : g ≠ h := by
      intro he
      apply hne
      simp [he]
    have hgTail : g ∉ tail := by
      intro hx
      apply hne
      exact List.mem_cons_of_mem h hx
    obtain ⟨hNotTail, hTailNodup⟩ :=
      List.nodup_cons.mp hnodup
    by_cases hr :
        oneGermBinaryRank m g ≥ oneGermBinaryRank m h
    · simpa [insertOneGermDescending, hr] using
        (List.nodup_cons.mpr ⟨hne, hnodup⟩)
    · have hNewTail : (insertOneGermDescending m g tail).Nodup :=
        ih hgTail hTailNodup
      have hNotNewTail :
          h ∉ insertOneGermDescending m g tail := by
        intro hx
        rcases (mem_insertOneGermDescending_iff m g h tail).mp hx with
          heq | hmem
        · exact hgNe heq.symm
        · exact hNotTail hmem
      simpa [insertOneGermDescending, hr] using
        (List.nodup_cons.mpr ⟨hNotNewTail, hNewTail⟩)

/-- The finite insertion sorter never duplicates a germ that was
distinct in the input. -/
theorem sortOneGermsDescending_nodup
    (m : Nat) (children : List (OneGermSpace m))
    (hnodup : children.Nodup) :
    (sortOneGermsDescending m children).Nodup := by
  induction children with
  | nil =>
    simp [sortOneGermsDescending]
  | cons g tail ih =>
    obtain ⟨hNotTail, hTailNodup⟩ :=
      List.nodup_cons.mp hnodup
    have hNotSorted :
        g ∉ sortOneGermsDescending m tail := by
      intro h
      exact hNotTail
        ((mem_sortOneGermsDescending_iff m g tail).mp h)
    change
      (insertOneGermDescending m g
        (sortOneGermsDescending m tail)).Nodup
    exact insertOneGermDescending_nodup m g _
      hNotSorted (ih hTailNodup)

/-- In every ORIGINAL cut block, the sorted selected singleton
germ labels remain a genuine set: no selected event class is
inserted twice, even for a countable source pre-diary. -/
theorem selectedOneGerms_sorted_nodup
    (H : Ordered3Graph Nat) (m : Nat) :
    (sortOneGermsDescending m
      (selectedOneGerms H m).toList).Nodup := by
  classical
  apply sortOneGermsDescending_nodup
  exact Finset.nodup_toList _

end DiaryLeafPriority
end ThreeUniformDiaries
