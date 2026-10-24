import ThreeUniformDiaries.DiaryFiniteSignRootedRawAmalgam

/-!
# Terminal support of the induced raw sign-rooted flip tree

The sign-rooted raw amalgam shares exact prefix nodes. If an
edge terminates at a node of a chosen branch i, its two earlier
vertices must be the corresponding earlier prefix nodes of i:
no off-branch vertex can occur in the middle of a raw edge
terminating on i. The actual source branch edge bit is then
determined by the sign-rooted E1--E5 prefix theorem.

This is the essential ZERO-OFF-BRANCH principle needed for
V1/V2 gluing at shared split nodes. It is a property of the RAW
relational union only. Adding cross-branch Devlin marker edges
can change the singleton and pair-type tests, so this theorem
alone does NOT construct a V/E pre-diary or an absorber.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace FiniteSignRootedFlipFamily

variable {A : Ordered3Graph Nat} {n : Nat} {ι : Type*}

/-- Every raw edge ending at a chosen branch node literally
comes from that SAME branch, with its two earlier vertices
on that branch and the correct source edge bit. -/
theorem rawAmalgam_edge_last_iff_on_branch
    (F : FiniteSignRootedFlipFamily A n ι)
    (i : ι) (X Y : FiniteSignRootedNode A n) (z : Nat) :
    (F.rawAmalgam).edge X Y (F.node i z) ↔
      ∃ x y : Nat, x < y ∧ y < z ∧ z < n ∧
        X = F.node i x ∧ Y = F.node i y ∧
        (F.graph i).edge x y z := by
  constructor
  · rintro ⟨j,x,y,w,hxy,hyw,hwn,hX,hY,hW,hE⟩
    have hwz : w = z := by
      have hv := congrArg Prod.fst hW
      simpa only [node_level] using hv
    subst w
    have hXprefix : F.node j x = F.node i x :=
      F.node_prefix_eq_of_terminal_eq j i x z (by omega) hW
    have hYprefix : F.node j y = F.node i y :=
      F.node_prefix_eq_of_terminal_eq j i y z (by omega) hW
    have hEdge : (F.graph i).edge x y z :=
      (F.edge_agree_of_shared_terminal_node
        j i x y z hxy hyw hwn hW).mp hE
    exact ⟨x,y,hxy,hyw,hwn,hX.symm.trans hXprefix,
      hY.symm.trans hYprefix,hEdge⟩
  · rintro ⟨x,y,hxy,hyz,hzn,hX,hY,hE⟩
    exact ⟨i,x,y,z,hxy,hyz,hzn,hX.symm,hY.symm,rfl,hE⟩

/-- Under an actual raw edge terminating on branch i, BOTH
earlier nodes are necessarily on that branch at their
corresponding original source levels. -/
theorem rawAmalgam_edge_last_prefix_nodes
    (F : FiniteSignRootedFlipFamily A n ι)
    (i : ι) (X Y : FiniteSignRootedNode A n) (z : Nat)
    (hEdge : (F.rawAmalgam).edge X Y (F.node i z)) :
    X = F.node i X.1 ∧ Y = F.node i Y.1 := by
  obtain ⟨x,y,_hxy,_hyz,_hzn,hX,hY,_hSource⟩ :=
    (F.rawAmalgam_edge_last_iff_on_branch i X Y z).mp hEdge
  have hx : X.1 = x := by rw [hX]; exact F.node_level i x
  have hy : Y.1 = y := by rw [hY]; exact F.node_level i y
  constructor
  · calc
      X = F.node i x := hX
      _ = F.node i X.1 := by rw [hx]
  · calc
      Y = F.node i y := hY
      _ = F.node i Y.1 := by rw [hy]

/-- Any off-path earlier node makes the raw edge test
automatically false at a prescribed terminal branch node.
The actual cross-branch marker completion is excluded. -/
theorem rawAmalgam_no_offpath_edge_at_terminal
    (F : FiniteSignRootedFlipFamily A n ι)
    (i : ι) (X Y : FiniteSignRootedNode A n) (z : Nat)
    (hOff : X ≠ F.node i X.1 ∨
      Y ≠ F.node i Y.1) :
    ¬ (F.rawAmalgam).edge X Y (F.node i z) := by
  intro h
  obtain ⟨hX,hY⟩ :=
    F.rawAmalgam_edge_last_prefix_nodes i X Y z h
  rcases hOff with hOffX | hOffY
  · exact hOffX hX
  · exact hOffY hY

end FiniteSignRootedFlipFamily
end DiaryLeafPriority
end ThreeUniformDiaries
