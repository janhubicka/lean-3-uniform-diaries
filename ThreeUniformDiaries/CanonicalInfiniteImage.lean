import ThreeUniformDiaries.CanonicalExactMeets
import ThreeUniformDiaries.InfinitePrefixes

/-!
# From an abstract canonical map to a coherent infinite image hypergraph

The manuscript forms an infinite hypergraph as the union of the nested
mapped finite enumeration prefixes.  We avoid selecting an inverse of
the skipped-level map: declare an ambient triple to be an image edge if
it appears in any mapped prefix whose target level contains that triple.

Selected-level restriction makes this independent of the witnessing
prefix.  Each selected target initial segment is then literally the
corresponding canonical image of the source initial segment, which
gives an induced infinite embedding on the selected vertex positions.

This supplies a concrete countable target hypergraph for the infinite
branch clause of the auxiliary Ramsey proof, without assuming that
the target is itself the generic hypergraph.
-/

namespace ThreeUniformDiaries
namespace CanonicalMap

/-- Coherence of the canonical images of finite initial segments. -/
theorem mappedPrefix_truncate
    (F : CanonicalMap) (H : Ordered3Graph Nat)
    {n m : Nat} (hnm : n ≤ m) :
    (F.mapEnum m (H.initialSegment m)).truncate (F.level n) =
      F.mapEnum n (H.initialSegment n) := by
  rw [← F.truncate_compat (H.initialSegment m) hnm]
  rw [H.initialSegment_truncate hnm]

/-- The mapped Boolean edge at a target position is independent of
which sufficiently long source prefix was chosen. -/
theorem mappedPrefix_triple_agree
    (F : CanonicalMap) (H : Ordered3Graph Nat)
    {n m i j k : Nat}
    (hkn : k < F.level n) (hkm : k < F.level m) :
    (F.mapEnum n (H.initialSegment n)).triple i j k =
      (F.mapEnum m (H.initialSegment m)).triple i j k := by
  let E := F.mapEnum (max n m) (H.initialSegment (max n m))
  have hL := F.mappedPrefix_truncate H (Nat.le_max_left n m)
  have hR := F.mappedPrefix_truncate H (Nat.le_max_right n m)
  have hbitL := congrArg (fun A : EnumNode (F.level n) =>
      A.triple i j k) hL
  have hbitR := congrArg (fun A : EnumNode (F.level m) =>
      A.triple i j k) hR
  have hEqL : (E.truncate (F.level n)).triple i j k =
      E.triple i j k := by
    simp [EnumNode.truncate, hkn]
  have hEqR : (E.truncate (F.level m)).triple i j k =
      E.triple i j k := by
    simp [EnumNode.truncate, hkm]
  calc
    (F.mapEnum n (H.initialSegment n)).triple i j k =
        (E.truncate (F.level n)).triple i j k := hbitL.symm
    _ = E.triple i j k := hEqL
    _ = (E.truncate (F.level m)).triple i j k := hEqR.symm
    _ = (F.mapEnum m (H.initialSegment m)).triple i j k := hbitR

/-- The target hypergraph is the coherent union of mapped prefixes. -/
def imageGraph (F : CanonicalMap) (H : Ordered3Graph Nat) :
    Ordered3Graph Nat where
  edge i j k :=
    ∃ n : Nat, k < F.level n ∧
      (F.mapEnum n (H.initialSegment n)).triple i j k = true

/-- Every selected target prefix is exactly its source's canonical image. -/
theorem imageGraph_initialSegment_eq
    (F : CanonicalMap) (H : Ordered3Graph Nat) (n : Nat) :
    (F.imageGraph H).initialSegment (F.level n) =
      F.mapEnum n (H.initialSegment n) := by
  classical
  apply EnumNode.ext_triples
  funext i j k
  let A := F.mapEnum n (H.initialSegment n)
  by_cases hvalid : i < j ∧ j < k ∧ k < F.level n
  · have hkn : k < F.level n := hvalid.2.2
    have hedge : (F.imageGraph H).edge i j k ↔ A.triple i j k = true := by
      constructor
      · rintro ⟨m, hkm, hm⟩
        have hagree := F.mappedPrefix_triple_agree H hkn hkm
        exact hagree ▸ hm
      · intro hbit
        exact ⟨n, hkn, hbit⟩
    by_cases hbit : A.triple i j k = true
    · have he : (F.imageGraph H).edge i j k := hedge.mpr hbit
      simp [Ordered3Graph.initialSegment, hvalid.1,
        hvalid.2.1, hvalid.2.2, he, A, hbit]
    · have hnedge : ¬ (F.imageGraph H).edge i j k := by
        intro he
        exact hbit (hedge.mp he)
      have hfalse : A.triple i j k = false := by
        cases hval : A.triple i j k with
        | false => rfl
        | true => exact False.elim (hbit hval)
      simp [Ordered3Graph.initialSegment, hvalid.1,
        hvalid.2.1, hvalid.2.2, hnedge, A, hfalse]
  · have hz : A.triple i j k = false := A.support i j k hvalid
    have hfalse : ¬ (i < j ∧ j < k ∧
        k < F.level n ∧ (F.imageGraph H).edge i j k) := by
      intro h
      exact hvalid ⟨h.1, h.2.1, h.2.2.1⟩
    simp [Ordered3Graph.initialSegment, hfalse, A, hz]

/-- The selected level map preserves and reflects all increasing edges
of an arbitrary infinite source, not just one finite prefix. -/
theorem imageGraph_selected_edges
    (F : CanonicalMap) (H : Ordered3Graph Nat)
    {i j k : Nat} (hij : i < j) (hjk : j < k) :
    (F.imageGraph H).edge (F.level i) (F.level j) (F.level k) ↔
      H.edge i j k := by
  have hk : F.level k < F.level (k + 1) :=
    F.strictMono (Nat.lt_succ_self k)
  calc
    (F.imageGraph H).edge (F.level i) (F.level j) (F.level k) ↔
        ((F.imageGraph H).initialSegment (F.level (k + 1))).triple
          (F.level i) (F.level j) (F.level k) = true :=
      ((F.imageGraph H).initialSegment_edge_iff
        (F.strictMono hij) (F.strictMono hjk) hk).symm
    _ ↔ (F.mapEnum (k + 1) (H.initialSegment (k + 1))).triple
          (F.level i) (F.level j) (F.level k) = true := by
      rw [F.imageGraph_initialSegment_eq H (k + 1)]
    _ ↔ (H.initialSegment (k + 1)).triple i j k = true := by
      rw [F.enum_triple_compat (H.initialSegment (k + 1))
        hij hjk (Nat.lt_succ_self k)]
    _ ↔ H.edge i j k :=
      H.initialSegment_edge_iff hij hjk (Nat.lt_succ_self k)

end CanonicalMap
end ThreeUniformDiaries
