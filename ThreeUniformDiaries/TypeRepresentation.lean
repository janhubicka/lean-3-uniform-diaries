import ThreeUniformDiaries.TypeTrees
import ThreeUniformDiaries.AuxTypes

/-!
# Type-hypergraph representations

The manuscript first defines singleton and auxiliary type equivalence through
agreement of edge predicates below a cut, then represents those types by
finite hypergraphs with distinguished type vertices. This file verifies
that the two definitions coincide.
-/

namespace ThreeUniformDiaries

namespace EnumNode

/-- Regard a finite enumerated hypergraph as an ordered edge predicate on
natural numbers, with all out-of-range triples absent. -/
def toOrdered3Graph {N : Nat} (H : EnumNode N) : Ordered3Graph Nat where
  edge i j k := H.triple i j k = true

@[simp] theorem toOrdered3Graph_edge {N i j k : Nat} (H : EnumNode N) :
    H.toOrdered3Graph.edge i j k ↔ H.triple i j k = true :=
  Iff.rfl

private theorem bool_eq_of_true_iff {x y : Bool}
    (h : (x = true ↔ y = true)) : x = y := by
  cases x <;> cases y <;> simp_all

/-- Equality of explicit 1-type nodes is exactly singleton-type agreement
below the cut. -/
theorem oneType_eq_iff_sameOneTypeBelow {N l u v : Nat} (H : EnumNode N) :
    H.oneType l u = H.oneType l v ↔
      (H.toOrdered3Graph).SameOneTypeBelow l u v := by
  constructor
  · intro hh i j hij hjl
    have hp := congrArg (fun t : OneNode l => t.pair i j) hh
    have heq : H.triple i j u = H.triple i j v := by
      simpa [EnumNode.oneType, hjl] using hp
    change H.triple i j u = true ↔ H.triple i j v = true
    rw [heq]
  · intro hh
    apply OneNode.ext_pairs
    funext i j
    change (if j < l then H.triple i j u else false) =
      (if j < l then H.triple i j v else false)
    by_cases hjl : j < l
    · simp only [if_pos hjl]
      by_cases hij : i < j
      · exact bool_eq_of_true_iff (hh hij hjl)
      · have hu : H.triple i j u = false := by
          apply H.support i j u
          intro hv
          exact hij hv.1
        have hv : H.triple i j v = false := by
          apply H.support i j v
          intro hw
          exact hij hw.1
        rw [hu, hv]
    · simp [hjl]

/-- Equality of explicit auxiliary-type nodes is exactly agreement of
the two pair types below the cut. -/
theorem auxType_eq_iff_sameAuxTypeBelow
    {N l u₀ u₁ v₀ v₁ : Nat} (H : EnumNode N) :
    H.auxType l u₀ u₁ = H.auxType l v₀ v₁ ↔
      (H.toOrdered3Graph).SameAuxTypeBelow l u₀ u₁ v₀ v₁ := by
  constructor
  · intro hh i hil
    have hp := congrArg (fun t : AuxNode l => t.bit i) hh
    have heq : H.triple i u₀ u₁ = H.triple i v₀ v₁ := by
      simpa [EnumNode.auxType, hil] using hp
    change H.triple i u₀ u₁ = true ↔ H.triple i v₀ v₁ = true
    rw [heq]
  · intro hh
    apply AuxNode.ext_bits
    funext i
    change (if i < l then H.triple i u₀ u₁ else false) =
      (if i < l then H.triple i v₀ v₁ else false)
    by_cases hil : i < l
    · simp only [if_pos hil]
      exact bool_eq_of_true_iff (hh hil)
    · simp [hil]

end EnumNode
end ThreeUniformDiaries
