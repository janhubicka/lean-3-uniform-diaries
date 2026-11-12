import ThreeUniformDiaries.DiaryFunctionalCandidateOldSupport

/-!
# Track A: only genuinely new supported triples require incidence checks

Fix an actual old admissible stage P and a proposed fresh target image v.
If the proposed complete numeric S1/S2 generator table is functional,
its canonical map q already equals P's map f on the ENTIRE old support
S_m, by the independently kernel-verified old-support rigidity lemma.

Consequently the entire induced edge AND nonedge condition on S_(m+1)
is EQUIVALENT to checking only those triples of the new support that
contain at least one vertex OUTSIDE the old support S_m.

This is strictly stronger than saying every new incidence must involve
the new leaf m: a new S1/S2 generator may occur BELOW an old source
leaf and must be tested against other old vertices. No source/target
RoleDiary hypothesis, new target leaf role, candidate existence or
future reserve is required for this purely finite reduction.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Old-only triples require no additional incidence tests under a
functional new-leaf generator relation; the old stage already fixes
their exact induced edge and nonedge table.

The converse is just restriction of complete new-stage inducedness to
triples with a genuinely newly generated support vertex. -/
theorem AdmissibleCofinalDiaryStage.functional_candidate_induced_iff_fresh_triples
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m v : Nat}
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (hFunctional : FiniteGeneratorTableFunctional
      (candidateNewLeafGeneratorTable H K m f v)) :
    (∀ a b c : Nat,
      a ∈ countableDiaryFiniteSupport H (m + 1) →
      b ∈ countableDiaryFiniteSupport H (m + 1) →
      c ∈ countableDiaryFiniteSupport H (m + 1) →
      a < b → b < c →
      (a ∉ countableDiaryFiniteSupport H m ∨
        b ∉ countableDiaryFiniteSupport H m ∨
        c ∉ countableDiaryFiniteSupport H m) →
      (H.edge a b c ↔
        K.edge (candidateNewLeafTableMap H K m f v a)
          (candidateNewLeafTableMap H K m f v b)
          (candidateNewLeafTableMap H K m f v c))) ↔
    (∀ a b c : Nat,
      a ∈ countableDiaryFiniteSupport H (m + 1) →
      b ∈ countableDiaryFiniteSupport H (m + 1) →
      c ∈ countableDiaryFiniteSupport H (m + 1) →
      a < b → b < c →
      (H.edge a b c ↔
        K.edge (candidateNewLeafTableMap H K m f v a)
          (candidateNewLeafTableMap H K m f v b)
          (candidateNewLeafTableMap H K m f v c))) := by
  classical
  let q := candidateNewLeafTableMap H K m f v
  have hOld : ∀ u : Nat,
      u ∈ countableDiaryFiniteSupport H m → q u = f u :=
    P.functional_candidate_table_preserves_old_support hFunctional
  constructor
  · intro hFresh a b c ha hb hc hab hbc
    by_cases hAllOld :
        a ∈ countableDiaryFiniteSupport H m ∧
        b ∈ countableDiaryFiniteSupport H m ∧
        c ∈ countableDiaryFiniteSupport H m
    · obtain ⟨haOld, hbOld, hcOld⟩ := hAllOld
      have hInduced := P.induced_edge a b c
        haOld hbOld hcOld hab hbc
      change H.edge a b c ↔ K.edge (q a) (q b) (q c)
      rw [hOld a haOld, hOld b hbOld, hOld c hcOld]
      exact hInduced
    · have hNew :
          a ∉ countableDiaryFiniteSupport H m ∨
          b ∉ countableDiaryFiniteSupport H m ∨
          c ∉ countableDiaryFiniteSupport H m := by
        tauto
      exact hFresh a b c ha hb hc hab hbc hNew
  · intro hAll a b c ha hb hc hab hbc _hNew
    exact hAll a b c ha hb hc hab hbc

end DiaryLeafPriority
end ThreeUniformDiaries
