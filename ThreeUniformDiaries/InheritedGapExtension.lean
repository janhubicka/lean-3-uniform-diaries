import ThreeUniformDiaries.GenericSourceStep
import ThreeUniformDiaries.BranchTypeAgreement

/-!
# Repair of the skipped-vertex step in Lemma lem:Kiemb

The old condition (C2) set every pair involving a skipped target
vertex to zero only below the preceding *global* image. This is
insufficient to preserve the singleton type at the current image,
because the current choice may skip further target vertices.

The correct finite instruction has two clauses for pairs not entirely
in the previously selected image:

* below the image of the immediate **branch predecessor** of the new
  K_I node, copy the edge bit of that predecessor;
* between the predecessor and the previous global image, choose zero.

Both clauses concern a finite initial segment and are therefore
simultaneously available from the generic extension property.

The abstract lemmas at the end show that the copy clause preserves all
gap bits across an entire branch, while the zero clause makes every
auxiliary-type test involving an omitted vertex vanish. The remaining
bookkeeping is to incorporate the conditions into the order-respecting
enumeration of K_I and carry out the exact-meet argument.
-/

namespace ThreeUniformDiaries

namespace GenericEnumerated3Graph

/-- The next-vertex pattern: prescribe the source edge on pairs of
selected images; on every other pair below the branch predecessor,
inherit that predecessor's old edge bit; above it, choose false. -/
noncomputable def gapInheritedPattern
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    {n m : Nat} (old : Fin n → Fin m) (parent : Fin m)
    (x y : Fin m) : Bool := by
  classical
  exact
    if ∃ i j : Fin n, i < j ∧ old i = x ∧ old j = y then
      decide (∃ i j : Fin n, i < j ∧ old i = x ∧
        old j = y ∧ K.edge i.val j.val n)
    else if y < parent then
      decide (G.graph.edge x.val y.val parent.val)
    else false

/-- The strengthened one-step generic extension needed by the repaired
construction. It does not assume the parent is the last enumerated
K_I vertex; only that the parent is among the old target vertices. -/
theorem exists_extension_inheriting_gaps
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (n m : Nat) (old : Fin n → Fin m) (hmono : StrictMono old)
    (parent : Fin m) :
    ∃ v : Nat, m ≤ v ∧
      (∀ i j : Fin n, i < j →
        (K.edge i.val j.val n ↔
         G.graph.edge (old i).val (old j).val v)) ∧
      (∀ x y : Fin m, x < y →
        ((¬ ∃ i : Fin n, old i = x) ∨
         (¬ ∃ j : Fin n, old j = y)) →
        y < parent →
        (G.graph.edge x.val y.val v ↔
         G.graph.edge x.val y.val parent.val)) ∧
      (∀ x y : Fin m, x < y →
        ((¬ ∃ i : Fin n, old i = x) ∨
         (¬ ∃ j : Fin n, old j = y)) →
        parent ≤ y →
        ¬ G.graph.edge x.val y.val v) := by
  classical
  obtain ⟨v, hv, hpat⟩ :=
    G.extension m (gapInheritedPattern G K old parent)
  refine ⟨v, hv, ?_, ?_, ?_⟩
  · intro i j hij
    have hsel :
        ∃ i' j' : Fin n,
          i' < j' ∧ old i' = old i ∧ old j' = old j :=
      ⟨i, j, hij, rfl, rfl⟩
    have hsource :
        (∃ i' j' : Fin n,
          i' < j' ∧ old i' = old i ∧ old j' = old j ∧
            K.edge i'.val j'.val n) ↔
        K.edge i.val j.val n := by
      constructor
      · rintro ⟨i', j', _, hi, hj, hEdge⟩
        have hieq : i' = i := hmono.injective hi
        have hjeq : j' = j := hmono.injective hj
        subst i'
        subst j'
        exact hEdge
      · intro hEdge
        exact ⟨i, j, hij, rfl, rfl, hEdge⟩
    have hbool :
        gapInheritedPattern G K old parent (old i) (old j) = true ↔
          K.edge i.val j.val n := by
      simp only [gapInheritedPattern, if_pos hsel, decide_eq_true_eq]
      exact hsource
    exact hbool.symm.trans
      ((hpat (old i) (old j) (hmono hij)).symm)
  · intro x y hxy hgap hy
    have hnot :
        ¬ ∃ i j : Fin n, i < j ∧ old i = x ∧ old j = y := by
      rintro ⟨i, j, _, hi, hj⟩
      rcases hgap with hx | hy'
      · exact hx ⟨i, hi⟩
      · exact hy' ⟨j, hj⟩
    have hp :
        gapInheritedPattern G K old parent x y = true ↔
          G.graph.edge x.val y.val parent.val := by
      simp [gapInheritedPattern, hnot, hy]
    exact (hpat x y hxy).trans hp
  · intro x y hxy hgap hy hEdge
    have hnot :
        ¬ ∃ i j : Fin n, i < j ∧ old i = x ∧ old j = y := by
      rintro ⟨i, j, _, hi, hj⟩
      rcases hgap with hx | hy'
      · exact hx ⟨i, hi⟩
      · exact hy' ⟨j, hj⟩
    have hp : gapInheritedPattern G K old parent x y = false := by
      simp [gapInheritedPattern, hnot, not_lt.mpr hy]
    have htrue := (hpat x y hxy).mp hEdge
    simp [hp] at htrue

end GenericEnumerated3Graph

namespace Ordered3Graph

/-- Along a branch, copying all pairs containing a globally omitted
vertex preserves their edge bits below any earlier chosen cut. -/
theorem gap_oneTypes_constant
    (H : Ordered3Graph Nat)
    (e : Nat → Nat) (he : Monotone e)
    (omitted : Nat → Prop)
    (hcopy : ∀ i x y : Nat, x < y → y < e i →
      (omitted x ∨ omitted y) →
      (H.edge x y (e (i + 1)) ↔ H.edge x y (e i)))
    (w u v x y : Nat) (hwu : w ≤ u) (hwv : w ≤ v)
    (hxy : x < y) (hyw : y < e w)
    (hgap : omitted x ∨ omitted y) :
    H.edge x y (e u) ↔ H.edge x y (e v) := by
  have hfrom :
      ∀ t : Nat, w ≤ t →
        (H.edge x y (e t) ↔ H.edge x y (e w)) := by
    intro t hwt
    induction t, hwt using Nat.le_induction with
    | base =>
        exact Iff.rfl
    | succ t hwt ih =>
        have hyt : y < e t := lt_of_lt_of_le hyw (he hwt)
        exact (hcopy t x y hxy hyt hgap).trans ih
  exact (hfrom u hwu).trans (hfrom v hwv).symm

/-- The zero-new-pair clause, together with inheritance at subsequent
branch vertices, forces every auxiliary test against an omitted vertex
to be a non-edge. -/
theorem gap_auxTypes_zero
    (H : Ordered3Graph Nat)
    (e : Nat → Nat) (he : StrictMono e)
    (omitted : Nat → Prop)
    (hcopy : ∀ i x y : Nat, x < y → y < e i →
      (omitted x ∨ omitted y) →
      (H.edge x y (e (i + 1)) ↔ H.edge x y (e i)))
    (hnew : ∀ i x : Nat, x < e i → omitted x →
      ¬ H.edge x (e i) (e (i + 1)))
    (u v x : Nat) (huv : u < v) (hx : x < e u)
    (hgap : omitted x) :
    ¬ H.edge x (e u) (e v) := by
  have hfrom :
      ∀ t : Nat, u + 1 ≤ t →
        ¬ H.edge x (e u) (e t) := by
    intro t hut
    induction t, hut using Nat.le_induction with
    | base =>
        exact hnew u x hx hgap
    | succ t hut ih =>
        have htu : u < t := by omega
        have hyt : e u < e t := he htu
        have hbits := hcopy t x (e u) hx hyt (Or.inl hgap)
        intro hEdge
        exact ih (hbits.mp hEdge)
  exact hfrom v (Nat.succ_le_iff.mpr huv)

end Ordered3Graph
end ThreeUniformDiaries
