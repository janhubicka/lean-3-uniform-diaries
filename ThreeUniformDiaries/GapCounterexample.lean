import ThreeUniformDiaries.BranchTypeAgreement

/-!
# The gap in the stated (C2) induction in lem:Kiemb

The manuscript requires (C2) only for pairs strictly below the *previous*
image vertex. It later invokes (C2) for all pairs below the *current*
image vertex. These are different cuts.

Here is a finite five-vertex source diagram from K_empty in an admissible
order: the length-1 and length-2 empty prefixes; both length-3
hypergraphs (non-edge and edge); then the length-4 empty prefix.
Its sole increasing hyperedge is (0,1,3).

Map these five nodes to target positions (0,1,5,6,7). Add to the target
only (0,1,6), required by (C1), and the uncontrolled gap edge (3,4,5).
The conditions (C1), (C2) at each of these five choices hold, but the
empty hypergraph's branch nodes at source vertices 2 and 3 are sent to
5 and 7. They have different singleton types below 5.

This counterexample refutes the deduction of the capped-meet case from
the *stated construction*. It does not refute the Ramsey theorem or the
possible existence of a more carefully chosen embedding.
-/

namespace ThreeUniformDiaries

private def gapSource : Ordered3Graph Nat where
  edge _ _ _ := False

private def gapTarget : Ordered3Graph Nat where
  edge a b c :=
    (a = 0 ∧ b = 1 ∧ c = 6) ∨ (a = 3 ∧ b = 4 ∧ c = 5)

/-- The finite induced hypergraph on five selected source K_empty nodes. -/
private def sourceDiagram : Ordered3Graph (Fin 5) where
  edge i j k := i.val = 0 ∧ j.val = 1 ∧ k.val = 3

/-- Consecutive source enumeration vertices go to 0, 1, 5, 6, 7. -/
private def imageAt (i : Fin 5) : Nat :=
  if i.val = 0 then 0
  else if i.val = 1 then 1
  else if i.val = 2 then 5
  else if i.val = 3 then 6
  else 7

/-- The source diagram is faithfully embedded, so (C1) holds. -/
theorem gapExample_preserves_all_induced_edges :
    ∀ i j k : Fin 5, i < j → j < k →
      (sourceDiagram.edge i j k ↔
       gapTarget.edge (imageAt i) (imageAt j) (imageAt k)) := by
  intro i j k hij hjk
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp_all [sourceDiagram, gapTarget, imageAt]

/-- The selected image vertices appear in increasing order. -/
theorem gapExample_image_strictMono : StrictMono imageAt := by
  decide

/-- The (C2) requirement when choosing the image 5 only covers
pairs below the previous image 1, not the newly skipped vertices 3,4. -/
theorem gapExample_step5_C2 (x y : Nat)
    (hxy : x < y) (hy : y < 2) :
    ¬ gapTarget.edge x y 5 := by
  simp only [gapTarget]
  omega

/-- At the next choice, 6, any possible edge uses the old image pair
(0,1), so every pair not entirely in the old image set is a non-edge. -/
theorem gapExample_step6_C2 (x y : Nat)
    (hout :
      x ∉ ({0, 1, 5} : Finset Nat) ∨
      y ∉ ({0, 1, 5} : Finset Nat)) :
    ¬ gapTarget.edge x y 6 := by
  intro h
  have h01 : x = 0 ∧ y = 1 := by
    simpa [gapTarget] using h
  rcases h01 with ⟨rfl, rfl⟩
  simp at hout

/-- At the last choice, 7, there are no incident edges at all. -/
theorem gapExample_step7_C2 (x y : Nat) :
    ¬ gapTarget.edge x y 7 := by
  simp [gapTarget]

/-- For the empty source hypergraph the singleton types of 2 and 3
agree through cut 2, but their selected target images 5 and 7
disagree at the previously skipped pair (3,4). -/
theorem gapExample_capped_meet_failure :
    gapSource.SameOneTypeBelow 2 2 3 ∧
      ¬ gapTarget.SameOneTypeBelow 5 5 7 := by
  constructor
  · intro a b hab hbl
    exact Iff.rfl
  · intro h
    have hw : gapTarget.edge 3 4 5 ↔ gapTarget.edge 3 4 7 :=
      h (by decide) (by decide)
    simp [gapTarget] at hw

end ThreeUniformDiaries
