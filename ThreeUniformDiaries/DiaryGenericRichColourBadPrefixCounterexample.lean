import ThreeUniformDiaries.DiaryGoodColourOnePointGenericCopy
import ThreeUniformDiaries.DiaryGenericE5PatternFibreCopy

/-!
# Track A: universal finite-prefix colour extension is NOT necessary for generic richness

English-first adversarial audit: 3-uniform-diaries PR #346.

For EVERY actual enumerated generic G, construct an ACTUAL
strictly increasing induced generic selfembedding u whose every
new vertex has the OPPOSITE old-pair E5 bit against {0,1} from
the original source triple (0,1,2).

The cofinal vertex colour C = {0,1} ∪ u[G] contains the WHOLE
induced generic G-copy u[G], yet the legitimate finite size-two
stage with images 0,1, bound 2, and both images in C cannot
be extended by ANY C vertex realizing G.edge 0 1 2.

Thus the previously verified HasGenericColourOnePointExtensions
condition suffices for generic richness, but its converse is
FALSE, already at the first nonvacuous n=2 prefix. A good-colour
proof should select a pruned sequence of geometrically safe
finite stages, rather than demand that EVERY C-coloured finite
stage is extendible.

C here is an arbitrary vertex predicate, NOT a complete genuine
diary old-cut colour; no false claim about a chosen anchored
reserved colour or countable diary unavoidability follows.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- In EVERY enumerated generic 3-hypergraph G there is a COFINAL
vertex subset C containing a whole strictly increasing induced
generic G selfcopy, with 0 and 1 additionally in C, such that
EVERY further C vertex v≥2 has the OPPOSITE old-pair E5 bit
from G.edge 0 1 2.

In particular C fails the universal finite-stage one-point
extension property on the perfectly valid identity two-vertex
stage. This is a concrete mathematical obstruction to treating
the sufficient finite-stage criterion as necessary. -/
theorem exists_cofinal_generic_rich_colour_with_bad_two_vertex_prefix
    (G : GenericEnumerated3Graph) :
    ∃ C : Nat → Prop,
      (∀ B : Nat, ∃ v : Nat, B < v ∧ C v) ∧
      (∃ u : Ordered3Graph.Embedding G.graph G.graph,
        ∀ i : Nat, C (u i)) ∧
      C 0 ∧ C 1 ∧
      (∀ v : Nat, 2 ≤ v → C v →
        (G.graph.edge 0 1 v ↔ ¬ G.graph.edge 0 1 2)) ∧
      ¬ HasGenericColourOnePointExtensions G C := by
  classical
  let A : Finset Nat := {0, 1}
  let q : Nat → Nat → Bool :=
    fun _ _ => decide (¬ G.graph.edge 0 1 2)
  obtain ⟨u, hAbove, _hOldAbove, hOldBits⟩ :=
    _root_.ThreeUniformDiaries.DiaryLeafPriority.GenericEnumerated3Graph.exists_induced_generic_selfcopy_in_oldPair_fibre
      G A q 2
  have hWrong (i : Nat) :
      G.graph.edge 0 1 (u i) ↔
        ¬ G.graph.edge 0 1 2 := by
    have h := hOldBits i 0 1
      (by simp [A]) (by simp [A]) (by omega)
    simpa [q, decide_eq_true_eq] using h
  let C : Nat → Prop :=
    fun t => t = 0 ∨ t = 1 ∨ ∃ i : Nat, u i = t
  have hBound (i : Nat) : i ≤ u i := by
    induction i with
    | zero => omega
    | succ n ih =>
        have hStep : u n < u (n + 1) :=
          u.strictMono (Nat.lt_succ_self n)
        omega
  have hCofinal : ∀ B : Nat, ∃ v : Nat, B < v ∧ C v := by
    intro B
    refine ⟨u (B + 1), ?_, ?_⟩
    · have h := hBound (B + 1)
      omega
    · exact Or.inr (Or.inr ⟨B + 1, rfl⟩)
  have hInCopy (i : Nat) : C (u i) :=
    Or.inr (Or.inr ⟨i, rfl⟩)
  have hZero : C 0 := Or.inl rfl
  have hOne : C 1 := Or.inr (Or.inl rfl)
  have hOpposite : ∀ v : Nat, 2 ≤ v → C v →
      (G.graph.edge 0 1 v ↔ ¬ G.graph.edge 0 1 2) := by
    intro v hv hCv
    rcases hCv with hv0 | hv1 | ⟨i, hi⟩
    · omega
    · omega
    · simpa only [hi] using hWrong i
  refine ⟨C, hCofinal, ⟨u, hInCopy⟩,
    hZero, hOne, hOpposite, ?_⟩
  intro hExt
  let s : FiniteGenericStage G G.graph 2 := {
    bound := 2
    image := fun i => i
    mono := by
      intro i j hij
      exact hij
    edge_iff := by
      intro i j k hij hjk
      have hk : k.val < 2 := k.isLt
      have hj : j.val < 2 := j.isLt
      omega
  }
  have hStageColour : ∀ i : Fin 2, C (s.image i).val := by
    intro i
    change C i.val
    by_cases hi : i.val = 0
    · exact Or.inl hi
    · have hiOne : i.val = 1 := by omega
      exact Or.inr (Or.inl hiOne)
  obtain ⟨v, hv, hCv, hNewBit⟩ := hExt s hStageColour
  have hRequested :
      G.graph.edge 0 1 2 ↔ G.graph.edge 0 1 v := by
    simpa [s] using hNewBit (0 : Fin 2) (1 : Fin 2) (by decide)
  have hOppositeV :=
    hOpposite v hv hCv
  by_cases hBit : G.graph.edge 0 1 2
  · have hAtV := hRequested.mp hBit
    exact (hOppositeV.mp hAtV) hBit
  · have hAtV := hOppositeV.mpr hBit
    exact hBit (hRequested.mpr hAtV)

end DiaryLeafPriority
end ThreeUniformDiaries
