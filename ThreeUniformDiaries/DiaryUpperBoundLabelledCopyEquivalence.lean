import ThreeUniformDiaries.DiaryUpperBoundDirectTransfer
import ThreeUniformDiaries.DiaryFiniteAutTorsor

/-!
# Track A: reconcile the two genuinely unordered labelled-copy interfaces

The direct upper-bound theorem uses `IsInducedLabelledCopy`,
which tests the source hypergraph on strictly increasing Fin a
triples, with the *unordered* target edge relation.

The exact marked-diary classifier uses `IsFiniteLabelledCopy`,
which tests every labelled triple (including arbitrary permutations).
For a genuine EnumNode source these are equivalent. It would be
wrong to silently infer this without proving symmetry and
irreflexivity of the unordered edge relation, because the source
labels of a copy need not follow their image's numerical order.

This bridge is purely finite, independent of diary axioms and the
existence of the target diary, and introduces no Ramsey or
unavoidability hypothesis.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

private theorem unorderedEdge_repeat_first_false
    (H : Ordered3Graph Nat) (x y : Nat) :
    ¬ H.unorderedEdge x x y := by
  unfold Ordered3Graph.unorderedEdge
  omega

private theorem unorderedEdge_repeat_middle_false
    (H : Ordered3Graph Nat) (x y : Nat) :
    ¬ H.unorderedEdge x y x := by
  unfold Ordered3Graph.unorderedEdge
  omega

private theorem unorderedEdge_repeat_last_false
    (H : Ordered3Graph Nat) (x y : Nat) :
    ¬ H.unorderedEdge x y y := by
  unfold Ordered3Graph.unorderedEdge
  omega

/-- The shorter increasing-label-copy predicate used by the
direct-upper theorem is EXACTLY the fully unordered labelled
finite-copy predicate used by the marked-diary classification.
No monotonicity of the target labelling is assumed. -/
theorem isInducedLabelledCopy_iff_fullUnordered
    {a : Nat} (A : EnumNode a)
    (K : Ordered3Graph Nat) (v : Fin a → Nat) :
    IsInducedLabelledCopy A K v ↔
      IsFiniteLabelledCopy A.toOrdered3Graph K a v := by
  constructor
  · rintro ⟨hvInj, hOnIncreasing⟩
    refine ⟨hvInj, ?_⟩
    have hOn (i j k : Fin a) (hij : i < j) (hjk : j < k) :
        A.toOrdered3Graph.unorderedEdge i.val j.val k.val ↔
          K.unorderedEdge (v i) (v j) (v k) := by
      exact
        (A.toOrdered3Graph.unorderedEdge_iff_of_lt
          i.val j.val k.val hij hjk).trans
        (hOnIncreasing i j k hij hjk)
    intro i j k
    by_cases hijEq : i = j
    · subst j
      have hS :=
        unorderedEdge_repeat_first_false A.toOrdered3Graph i.val k.val
      have hT := unorderedEdge_repeat_first_false K (v i) (v k)
      simp only [hS, hT]
    by_cases hikEq : i = k
    · subst k
      have hS :=
        unorderedEdge_repeat_middle_false A.toOrdered3Graph i.val j.val
      have hT := unorderedEdge_repeat_middle_false K (v i) (v j)
      simp only [hS, hT]
    by_cases hjkEq : j = k
    · subst k
      have hS :=
        unorderedEdge_repeat_last_false A.toOrdered3Graph i.val j.val
      have hT := unorderedEdge_repeat_last_false K (v i) (v j)
      simp only [hS, hT]
    by_cases hij : i < j
    · by_cases hjk : j < k
      · exact hOn i j k hij hjk
      · have hkj : k < j := by omega
        by_cases hik : i < k
        · calc
            A.toOrdered3Graph.unorderedEdge i.val j.val k.val ↔
                A.toOrdered3Graph.unorderedEdge i.val k.val j.val :=
              A.toOrdered3Graph.unorderedEdge_swap_last i.val j.val k.val
            _ ↔ K.unorderedEdge (v i) (v k) (v j) :=
              hOn i k j hik hkj
            _ ↔ K.unorderedEdge (v i) (v j) (v k) :=
              (K.unorderedEdge_swap_last (v i) (v j) (v k)).symm
        · have hki : k < i := by omega
          calc
            A.toOrdered3Graph.unorderedEdge i.val j.val k.val ↔
                A.toOrdered3Graph.unorderedEdge k.val i.val j.val :=
              A.toOrdered3Graph.unorderedEdge_rotate_back i.val j.val k.val
            _ ↔ K.unorderedEdge (v k) (v i) (v j) :=
              hOn k i j hki hij
            _ ↔ K.unorderedEdge (v i) (v j) (v k) :=
              (K.unorderedEdge_rotate_back (v i) (v j) (v k)).symm
    · have hji : j < i := by omega
      by_cases hik : i < k
      · calc
          A.toOrdered3Graph.unorderedEdge i.val j.val k.val ↔
              A.toOrdered3Graph.unorderedEdge j.val i.val k.val :=
            A.toOrdered3Graph.unorderedEdge_swap_first i.val j.val k.val
          _ ↔ K.unorderedEdge (v j) (v i) (v k) :=
            hOn j i k hji hik
          _ ↔ K.unorderedEdge (v i) (v j) (v k) :=
            (K.unorderedEdge_swap_first (v i) (v j) (v k)).symm
      · have hki : k < i := by omega
        by_cases hjk : j < k
        · calc
            A.toOrdered3Graph.unorderedEdge i.val j.val k.val ↔
                A.toOrdered3Graph.unorderedEdge j.val k.val i.val :=
              A.toOrdered3Graph.unorderedEdge_rotate i.val j.val k.val
            _ ↔ K.unorderedEdge (v j) (v k) (v i) :=
              hOn j k i hjk hki
            _ ↔ K.unorderedEdge (v i) (v j) (v k) :=
              (K.unorderedEdge_rotate (v i) (v j) (v k)).symm
        · have hkj : k < j := by omega
          calc
            A.toOrdered3Graph.unorderedEdge i.val j.val k.val ↔
                A.toOrdered3Graph.unorderedEdge k.val j.val i.val :=
              A.toOrdered3Graph.unorderedEdge_reverse i.val j.val k.val
            _ ↔ K.unorderedEdge (v k) (v j) (v i) :=
              hOn k j i hkj hji
            _ ↔ K.unorderedEdge (v i) (v j) (v k) :=
              (K.unorderedEdge_reverse (v i) (v j) (v k)).symm
  · rintro ⟨hvInj, hAll⟩
    refine ⟨hvInj, ?_⟩
    intro i j k hij hjk
    exact
      (A.toOrdered3Graph.unorderedEdge_iff_of_lt
        i.val j.val k.val hij hjk).symm.trans
      (hAll i j k)

end ATRFiniteDecoder
end ThreeUniformDiaries
