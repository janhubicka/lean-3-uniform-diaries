import ThreeUniformDiaries.DiaryExistenceUnconditional
import ThreeUniformDiaries.DiaryFiniteSupportInverseRank
import ThreeUniformDiaries.DiaryFiniteLeafMeetOnlySelectedLeaves

/-!
# Track B: exact finite leaf reduct by compression of the countable diary

For every finite initial segment [0,n) of an arbitrary ordered Nat
3-hypergraph H, the already proven unconditional countable diary
completion followed by the genuinely finite leaf-meet support
construction produces a finite full diary block whose leaves are
exactly an increasing induced copy of [0,n).

This avoids the false prediary universal old-cut assertion. The finite
frame bounds are explicit, and both edges AND nonedges are reflected.
No countable diary unavoidability, Ramsey theorem, or absorption enters.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

/-- An arbitrary finite ordered 3-hypergraph (represented by the
first n vertices of H) occurs increasingly and *inducedly* as
exactly all the leaves of a finite complete diary block.

The source may have any edge relation outside [0,n): it is ignored.
This covers the actual finite-source variant of diary existence,
not the false stronger prediary-completion assertion. -/
theorem exists_finite_diary_with_exact_induced_leaf_prefix
    (H : Ordered3Graph Nat) (n : Nat) :
    ∃ (F : Ordered3Graph Nat) (m : Nat) (f : Nat → Nat),
      FiniteRoleDiaryBlock F m ∧
      StrictMono f ∧
      (∀ u : Nat, u < n → f u < m ∧ IsLeaf F (f u)) ∧
      (∀ v : Nat, v < m → IsLeaf F v →
        ∃ u : Nat, u < n ∧ f u = v) ∧
      (∀ a b c : Nat, a < b → b < c → c < n →
        (F.edge (f a) (f b) (f c) ↔ H.edge a b c)) := by
  classical
  obtain ⟨D, hDiary, e, hLeaf, _⟩ :=
    exists_countable_full_diary_with_exact_leaf_reduct H
  let L : Finset Nat := (Finset.range n).image (fun u : Nat => e u)
  let S : Finset Nat := finiteLeafMeetSupport D L
  let F : Ordered3Graph Nat := finiteSupportGraph D S
  let f : Nat → Nat := finiteSupportLift S n (fun u => e u)
  have hL : ∀ x : Nat, x ∈ L → IsLeaf D x := by
    intro x hx
    obtain ⟨u,hu,hux⟩ := Finset.mem_image.mp hx
    exact hux ▸ hLeaf u
  have hRangeL : ∀ u : Nat, u < n → e u ∈ L := by
    intro u hu
    exact Finset.mem_image.mpr
      ⟨u, Finset.mem_range.mpr hu, rfl⟩
  have hRange : ∀ u : Nat, u < n → e u ∈ S := by
    intro u hu
    exact mem_finiteLeafMeetSupport_leaf D L (e u) (hRangeL u hu)
  have h0 : 0 ∈ S := mem_finiteLeafMeetSupport_marker D L 0 (by omega)
  have h1 : 1 ∈ S := mem_finiteLeafMeetSupport_marker D L 1 (by omega)
  have h2 : 2 ∈ S := mem_finiteLeafMeetSupport_marker D L 2 (by omega)
  have hMarkers := finiteSupportIndex_initial_markers S h0 h1 h2
  have hf : StrictMono f :=
    finiteSupportLift_strictMono S n (fun u => e u) e.strictMono hRange
  have hF : FiniteRoleDiaryBlock F S.card :=
    finiteLeafMeetSupport_is_finiteDiary hDiary hL
  refine ⟨F, S.card, f, hF, hf, ?_, ?_, ?_⟩
  · intro u hu
    have hs := finiteSupportLift_spec S n (fun u => e u) hRange u hu
    have hOldLeaf : IsLeaf D (e u) := hLeaf u
    have hIndex : finiteSupportIndex S (f u) = e u := hs.2
    have hf3 : 3 ≤ f u := by
      by_contra hn
      have hSmall : f u = 0 ∨ f u = 1 ∨ f u = 2 := by omega
      rcases hSmall with hRank0 | hRank1 | hRank2
      · rw [hRank0, hMarkers.2.1] at hIndex
        have hge := hOldLeaf.1
        omega
      · rw [hRank1, hMarkers.2.2.1] at hIndex
        have hge := hOldLeaf.1
        omega
      · rw [hRank2, hMarkers.2.2.2] at hIndex
        have hge := hOldLeaf.1
        omega
    refine ⟨hs.1, ?_⟩
    apply (finiteSupportGraph_leaf_iff
      (G := D) h0 h1 h2 (f u) hf3 hs.1).mpr
    simpa only [hIndex] using hOldLeaf
  · intro v hv hvLeaf
    have hv3 : 3 ≤ v := hvLeaf.1
    have hOldInL : finiteSupportIndex S v ∈ L :=
      finiteLeafMeetSupport_reindexed_leaf_mem_L
        hDiary hL v hv3 hv hvLeaf
    obtain ⟨u,hu,hEq⟩ := Finset.mem_image.mp hOldInL
    have hun : u < n := Finset.mem_range.mp hu
    refine ⟨u, hun, ?_⟩
    change finiteSupportLift S n (fun u => e u) u = v
    rw [finiteSupportLift_of_lt S n (fun u => e u) u hun]
    rw [hEq, finiteSupportRank_of_index S v hv]
  · intro a b c hab hbc hc
    have ha : a < n := by omega
    have hb : b < n := by omega
    have hfa := finiteSupportLift_spec S n (fun u => e u)
      hRange a ha
    have hfb := finiteSupportLift_spec S n (fun u => e u)
      hRange b hb
    have hfc := finiteSupportLift_spec S n (fun u => e u)
      hRange c hc
    have hfab : f a < f b := hf hab
    have hfbc : f b < f c := hf hbc
    change (finiteSupportGraph D S).edge (f a) (f b) (f c) ↔
      H.edge a b c
    calc
      (finiteSupportGraph D S).edge (f a) (f b) (f c) ↔
          D.edge (finiteSupportIndex S (f a))
            (finiteSupportIndex S (f b))
            (finiteSupportIndex S (f c)) :=
        finiteSupportGraph_edge_iff D S
          (f a) (f b) (f c) hfab hfbc hfc.1
      _ ↔ H.edge a b c := by
        rw [hfa.2, hfb.2, hfc.2]
        exact (e.edge_iff hab hbc).symm

end DiaryLeafPriority
end ThreeUniformDiaries
