import ThreeUniformDiaries.GenericExtensionStep
import ThreeUniformDiaries.DiaryRoleAxioms

/-!
# Arbitrarily late copies of every singleton type in the generic graph

The first step of the diary lower-bound type-stabilisation proof
avoids a finite set of forbidden target vertices by applying ATR to
all singleton types over the protected prefix.

The geometric input is the elementary generic extension property:
every singleton type over any fixed finite cut n is realised beyond
any prescribed B. The proof below applies genericity to a finite
pattern larger than *both* n and B, copying precisely the desired
edge bits on ordered pairs from the protected prefix. The
unprescribed bits are irrelevant.

This is the required unbounded-realisation fact, independently of
the subsequent Ramsey and finite-code arguments.
-/

namespace ThreeUniformDiaries
namespace GenericEnumerated3Graph

/-- Given any vertex a (not necessarily after n), realise its
singleton edge pattern below n at an arbitrarily late vertex v.
Both v >= n and v > B are guaranteed. -/
theorem exists_late_same_one_type
    (G : GenericEnumerated3Graph)
    (n a B : Nat) :
    ∃ v : Nat, n ≤ v ∧ B < v ∧
      G.graph.SameOneTypeBelow n a v := by
  classical
  let m := n + B + 1
  let pattern : Fin m → Fin m → Bool :=
    fun x y => decide (G.graph.edge x.val y.val a)
  obtain ⟨v, hvm, hv⟩ := G.extension m pattern
  refine ⟨v, ?_, ?_, ?_⟩
  · dsimp [m] at hvm
    omega
  · dsimp [m] at hvm
    omega
  · intro x y hxy hyn
    have hxm : x < m := by dsimp [m]; omega
    have hym : y < m := by dsimp [m]; omega
    have hbit := hv (⟨x, hxm⟩ : Fin m) (⟨y, hym⟩ : Fin m) hxy
    change G.graph.edge x y v ↔
      decide (G.graph.edge x y a) = true at hbit
    calc
      G.graph.edge x y a ↔
          decide (G.graph.edge x y a) = true := by simp
      _ ↔ G.graph.edge x y v := hbit.symm

/-- A simultaneous lower bound on the new vertex and a prescribed
finite protected prefix: any singleton type can be realised with
its vertex strictly past the requested bound. -/
theorem exists_late_same_one_type_with_cut
    (G : GenericEnumerated3Graph)
    (n a B : Nat) :
    ∃ v, max n (B+1) ≤ v ∧
      G.graph.SameOneTypeBelow n a v := by
  obtain ⟨v, hn, hB, htype⟩ :=
    G.exists_late_same_one_type n a B
  exact ⟨v, by omega, htype⟩

end GenericEnumerated3Graph
end ThreeUniformDiaries
