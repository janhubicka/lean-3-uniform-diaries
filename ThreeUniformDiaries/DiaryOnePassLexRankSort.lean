import ThreeUniformDiaries.DiaryOnePassSortedGermNodup

/-!
# Actual finite child-event schedule is decreasing in binary rank

Previously the singleton sorting algorithm was executable as a
finite insertion sort and was proved to preserve membership, length,
and absence of duplicate germs. We now verify the ORDER invariant
that V3 requires: for any two germs in the sorted list in list order,
the earlier germ has at least the binary rank of the later one.

Equal-rank germs need not have a stable relative order. The proof
only establishes weak decreasing rank; subsequent V3 work must
also establish that distinct same-parent next-cut singleton germs
have DISTINCT ranks (or explicitly resolve ties). We do not
assume source S1/S2 or the target diary axioms.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The actual descending insertion preserves pairwise rank order. -/
theorem insertOneGermDescending_pairwise_rank
    (m : Nat) (g : OneGermSpace m)
    (children : List (OneGermSpace m))
    (hOrdered : children.Pairwise
      (fun x y => oneGermBinaryRank m x ≥ oneGermBinaryRank m y)) :
    (insertOneGermDescending m g children).Pairwise
      (fun x y => oneGermBinaryRank m x ≥ oneGermBinaryRank m y) := by
  induction children with
  | nil =>
      simp [insertOneGermDescending]
  | cons h tail ih =>
      obtain ⟨hHead, hTail⟩ := List.pairwise_cons.mp hOrdered
      by_cases hr : oneGermBinaryRank m g ≥ oneGermBinaryRank m h
      · have hNewHead :
            ∀ x ∈ h :: tail,
              oneGermBinaryRank m g ≥ oneGermBinaryRank m x := by
          intro x hx
          rcases List.mem_cons.mp hx with heq | hmem
          · subst x
            exact hr
          · exact le_trans (hHead x hmem) hr
        have hSorted :
            (g :: h :: tail).Pairwise
              (fun x y => oneGermBinaryRank m x ≥
                oneGermBinaryRank m y) :=
          List.pairwise_cons.mpr ⟨hNewHead, hOrdered⟩
        simpa [insertOneGermDescending, hr] using hSorted
      · have hNewHead :
            ∀ x ∈ insertOneGermDescending m g tail,
              oneGermBinaryRank m h ≥ oneGermBinaryRank m x := by
          intro x hx
          rcases (mem_insertOneGermDescending_iff m g x tail).mp hx with
            heq | hmem
          · subst x
            omega
          · exact hHead x hmem
        have hSorted :
            (h :: insertOneGermDescending m g tail).Pairwise
              (fun x y => oneGermBinaryRank m x ≥
                oneGermBinaryRank m y) :=
          List.pairwise_cons.mpr ⟨hNewHead, ih hTail⟩
        simpa [insertOneGermDescending, hr] using hSorted

/-- Finite sorting really returns a list weakly decreasing in
the manuscript's source singleton-test binary numeral. -/
theorem sortOneGermsDescending_pairwise_rank
    (m : Nat) (children : List (OneGermSpace m)) :
    (sortOneGermsDescending m children).Pairwise
      (fun x y => oneGermBinaryRank m x ≥ oneGermBinaryRank m y) := by
  induction children with
  | nil =>
      simp [sortOneGermsDescending]
  | cons g tail ih =>
      change (insertOneGermDescending m g
        (sortOneGermsDescending m tail)).Pairwise
          (fun x y => oneGermBinaryRank m x ≥ oneGermBinaryRank m y)
      exact insertOneGermDescending_pairwise_rank m g _ ih

/-- The genuine selected events at every old leaf cut have the
decreasing-rank invariant, not just an intended scheduling rule. -/
theorem onePass_selectedOneGerms_pairwise_rank
    (H : Ordered3Graph Nat) (m : Nat) :
    (sortOneGermsDescending m
       (selectedOneGerms H m).toList).Pairwise
         (fun x y => oneGermBinaryRank m x ≥
           oneGermBinaryRank m y) :=
  sortOneGermsDescending_pairwise_rank m _

end DiaryLeafPriority
end ThreeUniformDiaries
