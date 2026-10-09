import ThreeUniformDiaries.FiniteSelectedSuccessorBridge
import ThreeUniformDiaries.FiniteSelectedSuccessorUnique
import ThreeUniformDiaries.FiniteActualCandidateMeetClosure

/-!
# An actual finite E2 candidate determines its next canonical image

Fix a genuine finite aux-type-respecting embedding A -> H and a
completed finite auxiliary strong picture containing the prescribed
E2^- nodes. For n <= i < u < v < m, the target pair type at selected
level f(i+1) is exactly the unique node in the next strong layer
lying above the ambient successor of the target pair type at f(i)
with the source edge bit A(i,u,v).

This is a concrete instance of the auxiliary-coordinate induction
needed for Lemma Aemb. It does not assume any artificial source
vertices after m and does not assume construction of the complete
canonical maps.
-/

namespace ThreeUniformDiaries
namespace EnumNode

theorem finiteAuxCandidate_next_is_unique
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (f : Nat → Nat)
    (hf : Ordered3Graph.FiniteAuxEmbedding
      A.toOrdered3Graph H.toOrdered3Graph f m)
    (n : Nat)
    {S : Set CoordNode} {root : CoordNode}
    (hS : CoordNode.FiniteStrongPicture S f (m - 1) root)
    (hinc : ∀ x, finiteAuxCandidate A H f n x → x ∈ S)
    (i u v : Nat)
    (hni : n ≤ i) (hiu : i < u) (huv : u < v) (hvm : v < m) :
    ∀ z : CoordNode,
      z ∈ S →
      CoordNode.level z = f (i + 1) →
      CoordNode.aux (f i + 1)
        ((H.auxType (f i) (f u) (f v)).succ (A.triple i u v)) ≤ z →
      z = CoordNode.aux (f (i + 1))
        (H.auxType (f (i + 1)) (f u) (f v)) := by
  have hik : i < m - 1 := by omega
  let p := CoordNode.aux (f i) (H.auxType (f i) (f u) (f v))
  let t := CoordNode.aux (f i + 1)
    ((H.auxType (f i) (f u) (f v)).succ (A.triple i u v))
  let q := CoordNode.aux (f (i + 1))
    (H.auxType (f (i + 1)) (f u) (f v))
  have hp : p ∈ S := hinc p (Or.inr
    ⟨i, u, v, hni, Nat.le_of_lt hiu, huv, hvm, rfl⟩)
  have hq : q ∈ S := hinc q (Or.inr
    ⟨i + 1, u, v, by omega, by omega, huv, hvm, rfl⟩)
  have htq : t ≤ q := by
    have hlt : f i < f (i + 1) :=
      hf.strictMono (Nat.lt_succ_self i)
    have hstep : f i + 1 ≤ f (i + 1) := by omega
    refine ⟨hstep, ?_⟩
    change CoordNode.aux (f i + 1)
        ((H.auxType (f (i + 1)) (f u) (f v)).truncate (f i + 1)) =
      CoordNode.aux (f i + 1)
        ((H.auxType (f i) (f u) (f v)).succ (A.triple i u v))
    exact congrArg (CoordNode.aux (f i + 1))
      (finite_selected_aux_successor A H f hf i u v hiu huv hvm)
  have hpt : p ≤ t := by
    refine ⟨by dsimp [p, t, CoordNode.level]; omega, ?_⟩
    simp [p, t, CoordNode.level, CoordNode.truncate]
  have hptCover : p ⋖ t := by
    apply SuccessorTree.LevelTree.covBy_of_le_level_succ hpt
    change CoordNode.level t = CoordNode.level p + 1
    rfl
  rcases hS with ⟨_, _, _, _, _, _, hchildren⟩
  obtain ⟨z0, hz0, hunique⟩ :=
    hchildren i hik p hp rfl t hptCover
  intro z hz hzlev htz
  exact (hunique z ⟨hz, hzlev, htz⟩).trans
    (hunique q ⟨hq, rfl, htq⟩).symm

end EnumNode
end ThreeUniformDiaries
