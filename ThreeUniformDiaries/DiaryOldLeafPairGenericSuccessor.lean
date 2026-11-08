import ThreeUniformDiaries.DiaryOuterGenericLeafPatternRealization
import ThreeUniformDiaries.DiaryUniformOldStageTailColour

/-!
# Track D: exact relative new-leaf incidence on ALL old selected leaf pairs

The positive generic-extension theorem from the preceding module
handles arbitrary finite Boolean patterns on old pairs of vertices
in ONE specified unordered generic image.

Here we APPLY it to a genuine old RESERVED DIARY STAGE on the
canonical complete support S_m. We no longer require the user to
supply a compatible pattern: the source hypergraph's requested
edges and nonedges H.edge(a,b,m) on all old selected pairs
a<b<m are packed into a finite target pair table by the existing
strict ordered stage map f.

Because f maps genuine old selected leaves into the prescribed
F[generic] range, genericity produces an actual new target leaf
F(t) after the old stage tail cut, realizing ALL such old-leaf-pair
edge bits simultaneously.

This is a genuine UNCONDITIONAL positive geometric subgoal of
the full successor test: no split/marker pair interactions,
S1/S2 new generator positions, table functionality, or
future-order reserves are claimed. The outer F need NOT be
order preserving.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- For ANY genuine old reserved stage using one designated
unordered generic leaf range, the NEXT fresh source leaf's
prescribed edge/nonedge relation to EVERY pair of old selected
source leaves can be realized by ONE actual new target leaf
of arbitrarily large image in the same designated range.

The fresh target leaf lies beyond the uniform old-stage tail
cut, so all old supported target vertices remain earlier.
This does not by itself make it a reserved diary successor:
the mixed marker/split incidences and forced S1/S2 meets
still need the full finite candidate table tests. -/
theorem exists_fresh_outer_generic_leaf_realizing_all_old_leaf_pair_bits
    {H K : Ordered3Graph Nat}
    (G : GenericEnumerated3Graph)
    (F : _root_.ThreeUniformDiaries.Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    (m : Nat) (f : Nat → Nat)
    (P : ReservedDiaryStage H K F m f) :
    ∃ t : Nat,
      oldStageTailCut H m f < F t ∧
      IsLeaf K (F t) ∧
      ∀ a b : Nat,
        a ∈ countableDiaryLeafPrefix H m →
        b ∈ countableDiaryLeafPrefix H m →
        a < b →
        (H.edge a b m ↔ K.edge (f a) (f b) (F t)) := by
  classical
  let L := countableDiaryLeafPrefix H m
  let B := L.sup f + 1
  let chi : Nat → Nat → Bool := fun x y =>
    decide (∃ a b : Nat,
      a ∈ L ∧ b ∈ L ∧ a < b ∧
      f a = x ∧ f b = y ∧ H.edge a b m)
  have hLeafSupport (a : Nat) (ha : a ∈ L) :
      a ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H L a ha
  have hLeaf (a : Nat) (ha : a ∈ L) : IsLeaf H a :=
    ((mem_countableDiaryLeafPrefix_iff H m a).mp ha).2.2
  have hInj : ∀ a b : Nat, a ∈ L → b ∈ L →
      f a = f b → a = b := by
    intro a b ha hb hEq
    rcases lt_trichotomy a b with hlt | hSame | hgt
    · have hOrder := P.1.ordered a b
        (hLeafSupport a ha) (hLeafSupport b hb) hlt
      omega
    · exact hSame
    · have hOrder := P.1.ordered b a
        (hLeafSupport b hb) (hLeafSupport a ha) hgt
      omega
  obtain ⟨t, hLate, hPat⟩ :=
    exists_outer_generic_vertex_realizing_bounded_pair_pattern
      G K F B (oldStageTailCut H m f) chi
  refine ⟨t, hLate, hFLeaf t, ?_⟩
  intro a b ha hb hab
  have hfa : a ∈ countableDiaryFiniteSupport H m :=
    hLeafSupport a ha
  have hfb : b ∈ countableDiaryFiniteSupport H m :=
    hLeafSupport b hb
  have hOrder : f a < f b := P.1.ordered a b hfa hfb hab
  obtain ⟨i, hi⟩ := P.1.leaf_range a hfa (hLeaf a ha)
  obtain ⟨j, hj⟩ := P.1.leaf_range b hfb (hLeaf b hb)
  have hB : f b < B :=
    lt_of_le_of_lt (Finset.le_sup (f := f) hb)
      (Nat.lt_succ_self _)
  have hTargetOrder : F i < F j := by
    simpa only [← hi, ← hj] using hOrder
  have hTargetBound : F j < B := by
    simpa only [← hj] using hB
  have hActual :
      K.edge (f a) (f b) (F t) ↔ chi (f a) (f b) = true := by
    simpa only [hi, hj] using hPat i j hTargetOrder hTargetBound
  have hChi :
      chi (f a) (f b) = true ↔ H.edge a b m := by
    change
      decide (∃ x y : Nat,
        x ∈ L ∧ y ∈ L ∧ x < y ∧
        f x = f a ∧ f y = f b ∧ H.edge x y m) = true ↔
        H.edge a b m
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨x, y, hx, hy, hxy, hfx, hfy, he⟩
      have hxa : x = a := hInj x a hx ha hfx
      have hyb : y = b := hInj y b hy hb hfy
      simpa only [hxa, hyb] using he
    · intro he
      exact ⟨a, b, ha, hb, hab, rfl, rfl, he⟩
  exact hChi.symm.trans hActual.symm

end DiaryLeafPriority
end ThreeUniformDiaries
