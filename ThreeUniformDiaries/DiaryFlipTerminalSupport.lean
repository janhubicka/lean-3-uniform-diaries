import ThreeUniformDiaries.DiaryFlipBranchAmalgam

/-!
# Exact terminal-branch support of the raw tree-of-flips amalgam

The raw union of branch edges has a crucial strong locality:
if an edge ends at a prefix node of branch i, its TWO earlier
vertices must be the corresponding earlier prefix nodes of i.
No off-path vertex can participate in a raw edge terminating
on i, even when that edge is witnessed by a different branch.

This is independent of the diary meet axioms. It follows from
the prefix uniqueness and the already-verified coherent induced
branch-amalgamation theorem.

It isolates the remaining cross-branch obstacle: the EXTRA
Devlin marker edges, not the raw branch edges, may introduce
new type tests involving an off-path earlier leaf. Any proof
of flip pre-diary completion must control precisely those
extra marker edges to preserve protected leaf and mixed meets.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RoleDiary
namespace FlipFamily

variable {A : Ordered3Graph Nat} {ι : Type*}

/-- Exact edge support at a chosen branch terminal: the edge is
present precisely when its first two vertices are on that branch
AND the corresponding original increasing triple is an edge. -/
theorem branchAmalgam_edge_last_iff_on_branch
    (T : FlipFamily A ι) (i : ι)
    (X Y : FlipNode) (z : Nat) :
    (T.branchAmalgam).edge X Y (T.node i z) ↔
      ∃ x y : Nat, x < y ∧ y < z ∧
        X = T.node i x ∧ Y = T.node i y ∧
        (T.graph i).edge x y z := by
  constructor
  · rintro ⟨j, x, y, w, hxy, hyw, hx, hy, hw, he⟩
    have hwz : w = z := by
      have hv := congrArg Prod.fst hw
      simpa only [node] using hv
    subst w
    have hxz : x < z := lt_trans hxy hyw
    have hpx : T.node j x = T.node i x :=
      T.node_prefix_eq_of_terminal_eq j i x z hxz.le hw
    have hpy : T.node j y = T.node i y :=
      T.node_prefix_eq_of_terminal_eq j i y z hyw.le hw
    have hedge : (T.graph i).edge x y z :=
      (T.edge_agree_of_shared_terminal_node
        j i x y z hxy hyw hw).mp he
    exact ⟨x, y, hxy, hyw, hx.symm.trans hpx,
      hy.symm.trans hpy, hedge⟩
  · rintro ⟨x, y, hxy, hyz, hx, hy, he⟩
    exact ⟨i, x, y, z, hxy, hyz, hx.symm, hy.symm,
      rfl, he⟩

/-- An edge with a prescribed branch terminal has no
off-branch earlier vertex, regardless of the witnessing
branch used to present the raw union. -/
theorem branchAmalgam_edge_last_prefix_nodes
    (T : FlipFamily A ι) (i : ι)
    (X Y : FlipNode) (z : Nat)
    (h : (T.branchAmalgam).edge X Y (T.node i z)) :
    X = T.node i X.1 ∧ Y = T.node i Y.1 := by
  obtain ⟨x, y, hxy, hyz, hx, hy, he⟩ :=
    (T.branchAmalgam_edge_last_iff_on_branch i X Y z).mp h
  have hX : X.1 = x := by
    rw [hx]
    exact T.node_level i x
  have hY : Y.1 = y := by
    rw [hy]
    exact T.node_level i y
  constructor
  · calc
      X = T.node i x := hx
      _ = T.node i X.1 := by rw [hX]
  · calc
      Y = T.node i y := hy
      _ = T.node i Y.1 := by rw [hY]

/-- A negative edge test involving an off-path earlier vertex
is automatic in the raw amalgam. New off-branch markers are
not part of this lemma. -/
theorem branchAmalgam_no_offpath_edge_at_terminal
    (T : FlipFamily A ι) (i : ι)
    (X Y : FlipNode) (z : Nat)
    (hOff : X ≠ T.node i X.1 ∨
      Y ≠ T.node i Y.1) :
    ¬ (T.branchAmalgam).edge X Y (T.node i z) := by
  intro he
  obtain ⟨hX, hY⟩ :=
    T.branchAmalgam_edge_last_prefix_nodes i X Y z he
  rcases hOff with hOffX | hOffY
  · exact hOffX hX
  · exact hOffY hY

end FlipFamily
end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
