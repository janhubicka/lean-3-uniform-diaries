import ThreeUniformDiaries.DiaryOnePassRealCodeColumn
import ThreeUniformDiaries.DiarySourceLexFirstAuxBit

/-!
# Actual new source-column tests and their auxiliary prefix agreement

OnePassSourceColumn stores Bool values of the genuine next-cut
singleton code on (q,m), q<m. Here we identify each indexed test
and show that auxiliary type agreement below q forces the
corresponding source column words to agree before q. No source
S1/S2, no output diary axiom and no raw Boolean-code injectivity.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Reading index i of the actual source column returns the
original genuine singleton-code coordinate (i,m). -/
theorem onePass_sourceColumn_getElem
    (H : Ordered3Graph Nat) (m u i : Nat) (hi : i < m) :
    (onePassSourceColumn H m u)[i]? =
      some ((oneCode H (m + 1) u)
        ⟨i, by omega⟩ ⟨m, by omega⟩) := by
  apply List.getElem?_eq_some_iff.mpr
  refine ⟨by simp [onePassSourceColumn, hi], ?_⟩
  simp [onePassSourceColumn, List.getElem_finRange]

/-- Source auxiliary type agreement exactly controls the tests
in the genuinely encoded new last column before the given cut q. -/
theorem onePass_sourceColumn_agree_before
    (H : Ordered3Graph Nat) (m u v q : Nat) (hq : q ≤ m)
    (hAgree : H.SameAuxTypeBelow q m u m v) :
    ∀ i : Nat, i < q →
      (onePassSourceColumn H m u)[i]? =
        (onePassSourceColumn H m v)[i]? := by
  intro i hi
  have him : i < m := by omega
  have hEdge : H.edge i m u ↔ H.edge i m v :=
    hAgree (a := i) hi
  have hBit : (oneCode H (m + 1) u)
      ⟨i, by omega⟩ ⟨m, by omega⟩ =
      (oneCode H (m + 1) v)
        ⟨i, by omega⟩ ⟨m, by omega⟩ := by
    classical
    simpa [oneCode, him] using
      congrArg (fun p : Prop => decide p) (propext hEdge)
  rw [onePass_sourceColumn_getElem H m u i him,
      onePass_sourceColumn_getElem H m v i him, hBit]

/-- A positive original edge at test (i,m,u) is equivalent to
the actual last-column Bool being true at index i. -/
theorem onePass_sourceColumn_true_iff
    (H : Ordered3Graph Nat) (m u i : Nat) (hi : i < m) :
    (onePassSourceColumn H m u)[i]? = some true ↔
      H.edge i m u := by
  classical
  rw [onePass_sourceColumn_getElem H m u i hi]
  simp [oneCode, hi]

/-- A negative original edge is equivalent to the same actual
last-column Bool being false at the given index. -/
theorem onePass_sourceColumn_false_iff
    (H : Ordered3Graph Nat) (m u i : Nat) (hi : i < m) :
    (onePassSourceColumn H m u)[i]? = some false ↔
      ¬ H.edge i m u := by
  classical
  rw [onePass_sourceColumn_getElem H m u i hi]
  simp [oneCode, hi]

end DiaryLeafPriority
end ThreeUniformDiaries
