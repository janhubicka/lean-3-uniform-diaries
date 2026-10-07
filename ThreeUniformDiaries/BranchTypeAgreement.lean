import ThreeUniformDiaries.RelativeBranchHypergraph

/-!
# Type agreement along universal finite-enumeration branches

The universal branch hypergraph contains vertices not on the given branch
`g_H`.  Nevertheless, at a fixed length cut, the *only* earlier nodes
that can create an edge with branch vertices are the corresponding
finite initial segments of H.  These facts isolate the chain argument in
the proof of manuscript Lemma `lem:Kiemb`.

The equivalences proved below quantify over **all** universal branch nodes,
not merely over vertices in the image of `g_H`.
They do not yet address the later enumeration of K_I or gaps in the
generic embedding into G.
-/

namespace ThreeUniformDiaries

namespace Ordered3Graph

/-- Normal form for an edge with one vertex on a fixed branch: its two
earlier vertices must be comparable and its middle vertex must be an
initial segment of the same enumerated hypergraph. -/
theorem universalBranch_edge_prefix_iff
    (H : Ordered3Graph Nat) (a b : EnumerationBranchNode)
    {u : Nat} (hab : a.last < b.last) (hbu : b.last < u) :
    universalBranchGraph.edge a b (H.branchNode u) ↔
      b.enumeration.truncate (a.last + 1) = a.enumeration ∧
      H.initialSegment (b.last + 1) = b.enumeration ∧
      H.edge a.last b.last u := by
  have hprefix :
      (H.initialSegment (u + 1)).truncate (b.last + 1) =
        H.initialSegment (b.last + 1) :=
    H.initialSegment_truncate (Nat.succ_le_succ hbu.le)
  have hedge :
      (H.initialSegment (u + 1)).triple a.last b.last u = true ↔
        H.edge a.last b.last u :=
    H.initialSegment_edge_iff hab hbu (Nat.lt_succ_self u)
  change
    (a.last < b.last ∧ b.last < u ∧
      b.enumeration.truncate (a.last + 1) = a.enumeration ∧
      (H.initialSegment (u + 1)).truncate (b.last + 1) =
        b.enumeration ∧
      (H.initialSegment (u + 1)).triple a.last b.last u = true) ↔
      _
  rw [hprefix, hedge]
  simp [hab, hbu]

/-- The complete singleton-type agreement at a length cut can be tested
against every pair of vertices of the universal branch hypergraph. -/
theorem universalBranch_sameOneTypeBelow_iff
    (H : Ordered3Graph Nat) (w u v : Nat)
    (hwu : w ≤ u) (hwv : w ≤ v) :
    (∀ a b : EnumerationBranchNode, a.last < b.last → b.last < w →
      (universalBranchGraph.edge a b (H.branchNode u) ↔
       universalBranchGraph.edge a b (H.branchNode v))) ↔
      H.SameOneTypeBelow w u v := by
  constructor
  · intro h a b hab hbw
    have hau : a < b := hab
    have hbu : b < u := lt_of_lt_of_le hbw hwu
    have hbv : b < v := lt_of_lt_of_le hbw hwv
    have hbranch := h (H.branchNode a) (H.branchNode b) hab hbw
    exact (H.branchNode_edge_iff hau hbu).symm.trans
      (hbranch.trans (H.branchNode_edge_iff hau hbv))
  · intro h a b hab hbw
    have hbu : b.last < u := lt_of_lt_of_le hbw hwu
    have hbv : b.last < v := lt_of_lt_of_le hbw hwv
    rw [H.universalBranch_edge_prefix_iff a b hab hbu,
      H.universalBranch_edge_prefix_iff a b hab hbv]
    have hedge : H.edge a.last b.last u ↔ H.edge a.last b.last v :=
      h hab hbw
    rw [hedge]

/-- Normal form for an edge through two vertices on a fixed branch.
The earlier auxiliary-test vertex either belongs to that branch at its
own level, or contributes no edge. -/
theorem universalBranch_edge_aux_prefix_iff
    (H : Ordered3Graph Nat) (a : EnumerationBranchNode)
    {u v : Nat} (hau : a.last < u) (huv : u < v) :
    universalBranchGraph.edge a (H.branchNode u) (H.branchNode v) ↔
      H.initialSegment (a.last + 1) = a.enumeration ∧
      H.edge a.last u v := by
  have hprefixA :
      (H.initialSegment (u + 1)).truncate (a.last + 1) =
        H.initialSegment (a.last + 1) :=
    H.initialSegment_truncate (Nat.succ_le_succ hau.le)
  have hprefixB :
      (H.initialSegment (v + 1)).truncate (u + 1) =
        H.initialSegment (u + 1) :=
    H.initialSegment_truncate (Nat.succ_le_succ huv.le)
  have hedge :
      (H.initialSegment (v + 1)).triple a.last u v = true ↔
        H.edge a.last u v :=
    H.initialSegment_edge_iff hau huv (Nat.lt_succ_self v)
  change
    (a.last < u ∧ u < v ∧
      (H.initialSegment (u + 1)).truncate (a.last + 1) =
        a.enumeration ∧
      (H.initialSegment (v + 1)).truncate (u + 1) =
        H.initialSegment (u + 1) ∧
      (H.initialSegment (v + 1)).triple a.last u v = true) ↔
      _
  rw [hprefixA, hprefixB, hedge]
  simp [hau, huv]

/-- The auxiliary type agrees below a cut precisely when all universal
branch-node tests below that cut agree. -/
theorem universalBranch_sameAuxTypeBelow_iff
    (H : Ordered3Graph Nat) (w u₀ u₁ v₀ v₁ : Nat)
    (hwu : w ≤ u₀) (hu : u₀ < u₁)
    (hwv : w ≤ v₀) (hv : v₀ < v₁) :
    (∀ a : EnumerationBranchNode, a.last < w →
      (universalBranchGraph.edge a (H.branchNode u₀) (H.branchNode u₁) ↔
       universalBranchGraph.edge a (H.branchNode v₀) (H.branchNode v₁))) ↔
      H.SameAuxTypeBelow w u₀ u₁ v₀ v₁ := by
  constructor
  · intro h a haw
    have hau : a < u₀ := lt_of_lt_of_le haw hwu
    have hav : a < v₀ := lt_of_lt_of_le haw hwv
    have hbranch := h (H.branchNode a) haw
    exact (H.branchNode_edge_iff hau hu).symm.trans
      (hbranch.trans (H.branchNode_edge_iff hav hv))
  · intro h a haw
    have hau : a.last < u₀ := lt_of_lt_of_le haw hwu
    have hav : a.last < v₀ := lt_of_lt_of_le haw hwv
    rw [H.universalBranch_edge_aux_prefix_iff a hau hu,
      H.universalBranch_edge_aux_prefix_iff a hav hv]
    have hedge : H.edge a.last u₀ u₁ ↔ H.edge a.last v₀ v₁ :=
      h haw
    rw [hedge]


/-- Restricting the universal tests to K_I does not lose information:
all the finite prefixes of H are still present in K_I. -/
theorem relativeBranch_sameOneTypeBelow_iff
    (H : Ordered3Graph Nat) {n : Nat}
    (I : EnumNode n) (hI : H.initialSegment n = I)
    (w u v : Nat) (hwu : w ≤ u) (hwv : w ≤ v) :
    (∀ a b : RelativeBranchNode I, a.val.last < b.val.last →
      b.val.last < w →
      ((relativeBranchGraph I).edge a b (H.relativeBranchNode I hI u) ↔
       (relativeBranchGraph I).edge a b (H.relativeBranchNode I hI v))) ↔
      H.SameOneTypeBelow w u v := by
  constructor
  · intro h a b hab hbw
    have hbranch :=
      h (H.relativeBranchNode I hI a)
        (H.relativeBranchNode I hI b) hab hbw
    change universalBranchGraph.edge
        (H.branchNode a) (H.branchNode b) (H.branchNode u) ↔
        universalBranchGraph.edge
        (H.branchNode a) (H.branchNode b) (H.branchNode v) at hbranch
    have hbu : b < u := lt_of_lt_of_le hbw hwu
    have hbv : b < v := lt_of_lt_of_le hbw hwv
    exact (H.branchNode_edge_iff hab hbu).symm.trans
      (hbranch.trans (H.branchNode_edge_iff hab hbv))
  · intro h a b hab hbw
    have huniversal :=
      (H.universalBranch_sameOneTypeBelow_iff w u v hwu hwv).mpr h
    exact huniversal a.val b.val hab hbw

/-- Likewise, restricting auxiliary-bit tests to K_I retains precisely
the original auxiliary type below the cut. -/
theorem relativeBranch_sameAuxTypeBelow_iff
    (H : Ordered3Graph Nat) {n : Nat}
    (I : EnumNode n) (hI : H.initialSegment n = I)
    (w u₀ u₁ v₀ v₁ : Nat)
    (hwu : w ≤ u₀) (hu : u₀ < u₁)
    (hwv : w ≤ v₀) (hv : v₀ < v₁) :
    (∀ a : RelativeBranchNode I, a.val.last < w →
      ((relativeBranchGraph I).edge a
          (H.relativeBranchNode I hI u₀) (H.relativeBranchNode I hI u₁) ↔
       (relativeBranchGraph I).edge a
          (H.relativeBranchNode I hI v₀) (H.relativeBranchNode I hI v₁))) ↔
      H.SameAuxTypeBelow w u₀ u₁ v₀ v₁ := by
  constructor
  · intro h a haw
    have hbranch := h (H.relativeBranchNode I hI a) haw
    change universalBranchGraph.edge
        (H.branchNode a) (H.branchNode u₀) (H.branchNode u₁) ↔
        universalBranchGraph.edge
        (H.branchNode a) (H.branchNode v₀) (H.branchNode v₁) at hbranch
    have hau : a < u₀ := lt_of_lt_of_le haw hwu
    have hav : a < v₀ := lt_of_lt_of_le haw hwv
    exact (H.branchNode_edge_iff hau hu).symm.trans
      (hbranch.trans (H.branchNode_edge_iff hav hv))
  · intro h a haw
    have huniversal :=
      (H.universalBranch_sameAuxTypeBelow_iff
        w u₀ u₁ v₀ v₁ hwu hu hwv hv).mpr h
    exact huniversal a.val haw

end Ordered3Graph
end ThreeUniformDiaries
