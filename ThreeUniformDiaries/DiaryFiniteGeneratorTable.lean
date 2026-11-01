import ThreeUniformDiaries.DiaryLeafGeneratedStageCompatibility

/-!
# A finite graph of forced images for leaf-generated diary supports

Every vertex of the generated support is a marker, selected leaf,
singleton meet of selected leaves, or full ordered-pair meet of
selected leaves. Given target leaf values q, record ALL generator
assignments (source vertex, forced target value) in a finite relation.

Duplicated source coordinates are deliberately retained until a
functionality test proves that all their target values coincide.
The source projection of this finite table is exactly the existing
finite leaf-meet support. This is a structural combinatorial
statement, independent of any relative-extension existence theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The finite relation of all images forced by a finite leaf map.
Unlike a prematurely chosen map, this records collisions between
distinct generators of the same source vertex. -/
noncomputable def finiteLeafGeneratorTable
    (H K : Ordered3Graph Nat) (L : Finset Nat)
    (q : Nat → Nat) : Finset (Nat × Nat) := by
  classical
  exact
    ((Finset.range 3).image (fun i : Nat => (i, i)) ∪
      L.image (fun a => (a,q a))) ∪
    ((((L.product L).filter (fun p : Nat × Nat => p.1 ≠ p.2)).image
      (fun p => (H.oneMeetLevel p.1 p.2,
        K.oneMeetLevel (q p.1) (q p.2)))) ∪
     (((finiteOrderedLeafPairs L).product (finiteOrderedLeafPairs L)).image
      (fun p => (H.twoMeetLevel p.1.1 p.1.2 p.2.1 p.2.2,
        K.twoMeetLevel (q p.1.1) (q p.1.2) (q p.2.1) (q p.2.2)))))

/-- Source projection of the full generator relation is precisely
the original finite support; no extra source vertices are introduced
and none of the generators is omitted. -/
theorem finiteLeafGeneratorTable_sources
    (H K : Ordered3Graph Nat) (L : Finset Nat)
    (q : Nat → Nat) :
    (finiteLeafGeneratorTable H K L q).image Prod.fst =
      finiteLeafMeetSupport H L := by
  classical
  simp [finiteLeafGeneratorTable, finiteLeafMeetSupport,
    finiteOneMeetSupport, finiteTwoMeetSupport,
    Finset.image_union, Finset.image_image, Function.comp_def]

/-- Every supported source vertex has at least one target entry
in the finite generator relation. No functional compatibility
of those entries is needed yet. -/
theorem finiteLeafGeneratorTable_covers_support
    (H K : Ordered3Graph Nat) (L : Finset Nat)
    (q : Nat → Nat)
    (u : Nat) (hu : u ∈ finiteLeafMeetSupport H L) :
    ∃ v : Nat, (u,v) ∈ finiteLeafGeneratorTable H K L q := by
  have hImage :
      u ∈ (finiteLeafGeneratorTable H K L q).image Prod.fst := by
    rw [finiteLeafGeneratorTable_sources H K L q]
    exact hu
  obtain ⟨⟨x,v⟩,hMem,hEq⟩ := Finset.mem_image.mp hImage
  have hx : x = u := by simpa using hEq
  subst x
  exact ⟨v,hMem⟩

/-- Finite compatibility of generator entries. -/
def FiniteGeneratorTableFunctional (T : Finset (Nat × Nat)) : Prop :=
  ∀ u v w : Nat, (u,v) ∈ T → (u,w) ∈ T → v = w

/-- Choose the forced target value for source coordinate u.
Outside the source projection return zero. Under functionality this
is the unique compatible value, independent of the chosen witness. -/
noncomputable def finiteGeneratorTableValue
    (T : Finset (Nat × Nat)) (u : Nat) : Nat := by
  classical
  exact if h : ∃ v : Nat, (u,v) ∈ T then Classical.choose h else 0

/-- Every row of a functional generator table determines the same
chosen image of its source coordinate. -/
theorem finiteGeneratorTableValue_eq_of_mem
    (T : Finset (Nat × Nat))
    (hFun : FiniteGeneratorTableFunctional T)
    (u v : Nat) (hMem : (u,v) ∈ T) :
    finiteGeneratorTableValue T u = v := by
  unfold finiteGeneratorTableValue
  split_ifs with h
  · exact hFun u (Classical.choose h) v (Classical.choose_spec h) hMem
  · exact False.elim (h ⟨v,hMem⟩)

/-- Generator table entries at all three markers. -/
theorem finiteLeafGeneratorTable_marker
    (H K : Ordered3Graph Nat) (L : Finset Nat)
    (q : Nat → Nat) (i : Nat) (hi : i < 3) :
    (i,i) ∈ finiteLeafGeneratorTable H K L q := by
  classical
  unfold finiteLeafGeneratorTable
  apply Finset.mem_union.mpr
  left
  apply Finset.mem_union.mpr
  left
  exact Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr hi,rfl⟩

/-- Generator entry for a selected leaf. -/
theorem finiteLeafGeneratorTable_leaf
    (H K : Ordered3Graph Nat) (L : Finset Nat)
    (q : Nat → Nat) (a : Nat) (ha : a ∈ L) :
    (a,q a) ∈ finiteLeafGeneratorTable H K L q := by
  classical
  unfold finiteLeafGeneratorTable
  apply Finset.mem_union.mpr
  left
  apply Finset.mem_union.mpr
  right
  exact Finset.mem_image.mpr ⟨a,ha,rfl⟩

/-- Generator entry for a singleton meet of two distinct
selected leaves. -/
theorem finiteLeafGeneratorTable_oneMeet
    (H K : Ordered3Graph Nat) (L : Finset Nat)
    (q : Nat → Nat) (a b : Nat)
    (ha : a ∈ L) (hb : b ∈ L) (hab : a ≠ b) :
    (H.oneMeetLevel a b,K.oneMeetLevel (q a) (q b)) ∈
      finiteLeafGeneratorTable H K L q := by
  classical
  have hPair : (a,b) ∈
      (L.product L).filter (fun p : Nat × Nat => p.1 ≠ p.2) :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨ha,hb⟩,hab⟩
  unfold finiteLeafGeneratorTable
  apply Finset.mem_union.mpr
  right
  apply Finset.mem_union.mpr
  left
  exact Finset.mem_image.mpr ⟨(a,b),hPair,rfl⟩

/-- Generator entry for a full meet of two ordered selected
leaf pairs; the two pairs themselves may coincide. -/
theorem finiteLeafGeneratorTable_twoMeet
    (H K : Ordered3Graph Nat) (L : Finset Nat)
    (q : Nat → Nat) (a b c d : Nat)
    (ha : a ∈ L) (hb : b ∈ L)
    (hc : c ∈ L) (hd : d ∈ L)
    (hab : a < b) (hcd : c < d) :
    (H.twoMeetLevel a b c d,
      K.twoMeetLevel (q a) (q b) (q c) (q d)) ∈
      finiteLeafGeneratorTable H K L q := by
  classical
  have hAB : (a,b) ∈ finiteOrderedLeafPairs L :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨ha,hb⟩,hab⟩
  have hCD : (c,d) ∈ finiteOrderedLeafPairs L :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hc,hd⟩,hcd⟩
  have hPair :
      ((a,b),(c,d)) ∈
        (finiteOrderedLeafPairs L).product (finiteOrderedLeafPairs L) :=
    Finset.mem_product.mpr ⟨hAB,hCD⟩
  unfold finiteLeafGeneratorTable
  apply Finset.mem_union.mpr
  right
  apply Finset.mem_union.mpr
  right
  exact Finset.mem_image.mpr ⟨((a,b),(c,d)),hPair,rfl⟩

end DiaryLeafPriority
end ThreeUniformDiaries
