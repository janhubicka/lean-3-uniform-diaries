import ThreeUniformDiaries.DiaryFiniteUniversalEdgeCode

/-!
# A finite diary universal for ALL finite diaries of a fixed bound

Every finite diary on the initial segment [0,n) has a finite
Boolean incidence code. There are only finitely many such codes,
and each code defining a genuine finite diary contributes one
bounded FiniteDiaryInput to our finite family. Invalid codes are
replaced by the harmless three-marker empty diary.

The already Lean-verified finite-family joint embedding theorem
then produces one genuinely FINITE diary containing a fully
induced, marker- and mixed-meet-preserving embedding of EVERY
finite diary of bound n.

This is stronger than the FIRST direction of the flip property:
every flip of a fixed source diary has the same bound n.
It is NOT the SECOND direction. A flip of this UNIVERSAL TARGET
may change its embedded copies, so every-flip absorption remains
a separate mathematical assertion.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The empty three-marker diagram is a genuine bounded finite
diary: it has no nonmarker vertices, leaves or split witnesses. -/
theorem finiteEmptyThree_diary :
    FiniteRoleDiaryBlock finiteEmptyThree 3 := by
  refine {
    prediary := finiteEmptyThree_prediary
    singleton_meets := ?_
    pair_meets := ?_
  }
  · intro a b _hab hb _ha hbLeaf
    have h3 : 3 ≤ b := hbLeaf.1
    omega
  · intro a b c d _hab _hcd hb _hd _ha hbLeaf _hc _hdLeaf
    have h3 : 3 ≤ b := hbLeaf.1
    omega

/-- Every finite Boolean code determines one ACTUAL finite diary
input: its own decoded graph when valid, the empty diagram when
invalid. No claim that every code describes a diary is made. -/
noncomputable def finiteDiaryInputOfCode
    (n : Nat) (code : FiniteDiaryEdgeCode n) :
    FiniteDiaryInput := by
  classical
  by_cases h : FiniteRoleDiaryBlock (finiteDiaryCodeGraph n code) n
  · exact {
      graph := finiteDiaryCodeGraph n code
      bound := n
      diary := h
    }
  · exact {
      graph := finiteEmptyThree
      bound := 3
      diary := finiteEmptyThree_diary
    }

/-- When the table IS a finite diary, its input is literally
that diary rather than the fallback. -/
theorem finiteDiaryInputOfCode_graph
    (n : Nat) (code : FiniteDiaryEdgeCode n)
    (h : FiniteRoleDiaryBlock (finiteDiaryCodeGraph n code) n) :
    (finiteDiaryInputOfCode n code).graph =
      finiteDiaryCodeGraph n code := by
  classical
  simp [finiteDiaryInputOfCode, h]

theorem finiteDiaryInputOfCode_bound
    (n : Nat) (code : FiniteDiaryEdgeCode n)
    (h : FiniteRoleDiaryBlock (finiteDiaryCodeGraph n code) n) :
    (finiteDiaryInputOfCode n code).bound = n := by
  classical
  simp [finiteDiaryInputOfCode, h]

/-- FINITE list of actual finite diary inputs, representing
all possible ordered ternary diary structures of bound n. -/
noncomputable def finiteDiaryCodeInputs
    (n : Nat) : List FiniteDiaryInput := by
  classical
  exact ((Finset.univ : Finset (FiniteDiaryEdgeCode n)).toList).map
    (finiteDiaryInputOfCode n)

/-- Every Boolean incidence table is represented in this
finite list, including those whose diary is the fallback. -/
theorem finiteDiaryInputOfCode_mem
    (n : Nat) (code : FiniteDiaryEdgeCode n) :
    finiteDiaryInputOfCode n code ∈ finiteDiaryCodeInputs n := by
  classical
  unfold finiteDiaryCodeInputs
  apply List.mem_map.mpr
  exact ⟨code, Finset.mem_toList.mpr (Finset.mem_univ code), rfl⟩

/-- Every genuine bounded finite diary is literally a member of
the represented list up to equality of its graph and bound. -/
theorem finiteDiaryCodeInputs_covers
    (n : Nat) (A : Ordered3Graph Nat)
    (DA : FiniteRoleDiaryBlock A n) :
    ∃ D : FiniteDiaryInput,
      D ∈ finiteDiaryCodeInputs n ∧
      D.graph = A ∧ D.bound = n := by
  classical
  let code := finiteDiaryEdgeCode A n
  have hGraph : finiteDiaryCodeGraph n code = A :=
    finiteDiaryCodeGraph_reconstruct A n DA.prediary.frame
  have hValid :
      FiniteRoleDiaryBlock (finiteDiaryCodeGraph n code) n := by
    rw [hGraph]
    exact DA
  refine ⟨finiteDiaryInputOfCode n code,
    finiteDiaryInputOfCode_mem n code, ?_, ?_⟩
  · exact (finiteDiaryInputOfCode_graph n code hValid).trans hGraph
  · exact finiteDiaryInputOfCode_bound n code hValid

/-- A SINGLE genuine finite diary contains exact protected
embeddings of EVERY finite diary of a given fixed bound n,
including all possible flips of such diaries.

This does NOT say that every flip of this target contains the
source; the universal target's flip may modify all these copies. -/
theorem exists_finiteDiary_universal_bound (n : Nat) :
    ∃ (T : Ordered3Graph Nat) (k : Nat),
      FiniteRoleDiaryBlock T k ∧
      ∀ (A : Ordered3Graph Nat), FiniteRoleDiaryBlock A n →
        ∃ f : Nat → Nat, FiniteMeetEmbedding A T n f := by
  classical
  obtain ⟨T,k,DT,hCopies⟩ :=
    exists_finiteDiary_for_finiteFamily (finiteDiaryCodeInputs n)
  refine ⟨T,k,DT,?_⟩
  intro A DA
  obtain ⟨D,hD,hGraph,hBound⟩ :=
    finiteDiaryCodeInputs_covers n A DA
  obtain ⟨f,hEmbedding⟩ := hCopies D hD
  refine ⟨f,?_⟩
  simpa only [hGraph,hBound] using hEmbedding

end DiaryLeafPriority
end ThreeUniformDiaries
