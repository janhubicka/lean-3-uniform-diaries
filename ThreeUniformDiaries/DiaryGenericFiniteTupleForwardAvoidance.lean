import ThreeUniformDiaries.DiaryGenericLocallyFiniteForwardAvoidance

/-!
# Track D: avoid a locally bounded relation to ANY finite old tuple

The pair-avoidance theorem already verified in the generic leaf source
is stronger than it first appears. If a relation R(A,y) to a future
vertex y is eventually false for every FIXED FINITE set A of old
vertices, then it can be encoded as ONE locally bounded binary
relation:

  Bad(x,y) ↔ ∃ A ⊆ {0,...,x}, R(A,y).

For each x there are only finitely many choices of A. Thus the
individual eventual absence of R(A,y) yields eventual absence of
Bad(x,y), uniformly over that entire finite powerset.

Apply the verified generic forward-pair avoidance theorem to Bad.
For every new selected vertex u(j) and every NONEMPTY finite set
A of previously selected vertices, its maximum source index is
below u(j-1). Consequently A ⊆ range (u(j-1)+1), and the binary
avoidance law implies ¬R(A,u(j)).

The selected selfcopy is a genuine induced generic hypergraph, and
its values under an arbitrary injective outer F remain STRICTLY
increasing in numerical target order. We never assume F monotone.

This is an obstruction to all locally finite old-tuple extension
relations, not an unconditional relative diary extension theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace GenericEnumerated3Graph

/-- Every locally target-bounded relation R(A,y), where A is an
arbitrary FINITE old-vertex set, can be avoided on one entire
induced generic selfcopy at ALL nonempty earlier selected
subsets, while simultaneously making F∘u strictly increasing.

The initial selected vertex has no nonempty earlier set, so the
assertion at j=0 is vacuous. The outer map F is injected but need
not be order preserving, and all selected edges/nonedges of the
generic 3-hypergraph survive in the induced selfcopy. -/
theorem exists_generic_selfembedding_avoiding_finite_old_sets
    (G : GenericEnumerated3Graph)
    (F : Nat → Nat) (hInj : Function.Injective F)
    (R : Finset Nat → Nat → Prop)
    (hFinite : ∀ A : Finset Nat, ∃ B : Nat,
      ∀ y : Nat, B ≤ F y → ¬ R A y) :
    ∃ u : Ordered3Graph.Embedding G.graph G.graph,
      StrictMono (fun i : Nat => F (u i)) ∧
      ∀ j : Nat, ∀ A : Finset Nat,
        A.Nonempty →
        (∀ x : Nat, x ∈ A → ∃ i : Nat, i < j ∧ x = u i) →
        ¬ R A (u j) := by
  classical
  let cutoff : Finset Nat → Nat := fun A =>
    Classical.choose (hFinite A)
  have hCutoff (A : Finset Nat) (y : Nat)
      (h : cutoff A ≤ F y) : ¬ R A y :=
    Classical.choose_spec (hFinite A) y h
  let Bad : Nat → Nat → Prop := fun x y =>
    ∃ A : Finset Nat,
      A ⊆ Finset.range (x + 1) ∧ R A y
  have hBoundBad : ∀ x : Nat, ∃ B : Nat,
      ∀ y : Nat, B ≤ F y → ¬ Bad x y := by
    intro x
    let family : Finset (Finset Nat) :=
      (Finset.range (x + 1)).powerset
    let B := family.sup cutoff
    refine ⟨B,?_⟩
    intro y hBy hBad
    obtain ⟨A,hSub,hRA⟩ := hBad
    have hMem : A ∈ family :=
      Finset.mem_powerset.mpr hSub
    have hAB : cutoff A ≤ B :=
      Finset.le_sup (f := cutoff) hMem
    exact (hCutoff A y (hAB.trans hBy)) hRA
  obtain ⟨u,hFMono,hAvoid⟩ :=
    exists_generic_selfembedding_avoiding_finite_forward
      G F hInj Bad hBoundBad
  refine ⟨u,hFMono,?_⟩
  intro j A hNonempty hEarlier
  cases j with
  | zero =>
      obtain ⟨x,hx⟩ := hNonempty
      obtain ⟨i,hi,_⟩ := hEarlier x hx
      omega
  | succ k =>
      intro hRA
      have hSub : A ⊆ Finset.range (u k + 1) := by
        intro x hx
        obtain ⟨i,hi,hxEq⟩ := hEarlier x hx
        have hik : i ≤ k := by omega
        have hUle : u i ≤ u k :=
          u.strictMono.monotone hik
        apply Finset.mem_range.mpr
        omega
      have hBad : Bad (u k) (u (k + 1)) :=
        ⟨A,hSub,hRA⟩
      exact (hAvoid k (k + 1) (Nat.lt_succ_self k)) hBad

end GenericEnumerated3Graph
end DiaryLeafPriority
end ThreeUniformDiaries
