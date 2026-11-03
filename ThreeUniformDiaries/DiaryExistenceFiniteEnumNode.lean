import ThreeUniformDiaries.DiaryExistenceFiniteExactLeafReduct
import ThreeUniformDiaries.TypeRepresentation

/-!
# Track B: finite diary existence for the intrinsic EnumNode source type

The original finite-prefix result uses an arbitrary Nat ordered
hypergraph H and a bound n. The manuscript quantifies instead over
ACTUAL finite ordered hypergraphs. These are represented directly by
EnumNode n, with no extra source-tail conditions.

Instantiate the previously verified finite-prefix construction at
A.toOrdered3Graph, and package its witness as a genuine map
Fin n -> Fin m. This makes the order-isomorphism onto EXACTLY the
finite diary leaves and induced edge/nonedge equivalence explicit.

The target is a FiniteRoleDiaryBlock rather than the impossible
claim of a global RoleDiary on a zero-extended finite Nat carrier.
No role diary assumptions on A, countable unavoidability or Ramsey.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Every intrinsic finite enumerated ordered 3-hypergraph is the
entire increasing induced leaf reduct of a genuine bounded finite
diary. In particular this covers the n=0 and n<3 cases.

The map is between the actual finite vertex types, not an
infinite zero-extended carrier. -/
theorem exists_finite_diary_exact_EnumNode_leaf_reduct
    (n : Nat) (A : EnumNode n) :
    ∃ (F : Ordered3Graph Nat) (m : Nat) (f : Fin n → Fin m),
      FiniteRoleDiaryBlock F m ∧
      (∀ i j : Fin n, i < j → f i < f j) ∧
      (∀ i : Fin n, IsLeaf F (f i).val) ∧
      (∀ v : Fin m, IsLeaf F v.val → ∃ i : Fin n, f i = v) ∧
      (∀ i j k : Fin n, i < j → j < k →
        (F.edge (f i).val (f j).val (f k).val ↔
          A.triple i.val j.val k.val = true)) := by
  classical
  obtain ⟨F, m, g, hDiary, hMono, hLeaves, hOnto, hEdges⟩ :=
    exists_finite_diary_with_exact_induced_leaf_prefix
      A.toOrdered3Graph n
  let f (i : Fin n) : Fin m :=
    ⟨g i.val, (hLeaves i.val i.isLt).1⟩
  refine ⟨F, m, f, hDiary, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    change g i.val < g j.val
    exact hMono (show i.val < j.val from hij)
  · intro i
    change IsLeaf F (g i.val)
    exact (hLeaves i.val i.isLt).2
  · intro v hv
    obtain ⟨u, hu, heq⟩ := hOnto v.val v.isLt hv
    refine ⟨⟨u,hu⟩, ?_⟩
    apply Fin.ext
    exact heq
  · intro i j k hij hjk
    change F.edge (g i.val) (g j.val) (g k.val) ↔
      A.triple i.val j.val k.val = true
    exact hEdges i.val j.val k.val
      (show i.val < j.val from hij)
      (show j.val < k.val from hjk) k.isLt

end DiaryLeafPriority
end ThreeUniformDiaries
