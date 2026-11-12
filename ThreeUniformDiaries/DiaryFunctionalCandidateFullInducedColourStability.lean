import ThreeUniformDiaries.DiaryFunctionalCandidateTerminalColourGate
import ThreeUniformDiaries.DiaryNewLeafMaxSupport

/-!
# Track A: entire candidate inducedness is stable under a fixed old-cut colour

Fix an ACTUAL old admissible stage P, a genuine next source leaf m,
and two proposed next target images v,w. Assume BOTH finite S1/S2
generator tables are functional, so the canonical maps really send m
to v and w. Assume they agree on every supported source coordinate
OTHER THAN m (one complete finite numeric generator profile) and
v,w have identical COMPLETE singleton colours at the cut determined
only by the old stage f.

If the first proposed value v is already a genuine full finite
candidate, the SECOND candidate's entire induced edge/nonedge table
is valid too. Every source support triple a<b<c has c≤m:
- when c<m, all three proposed target vertex images are IDENTICAL;
- when c=m, the already checked fixed-old-cut terminal incidence
  theorem transports every E2/E3/E5 terminal bit and nonbit.

Thus backward incidences at NEW splits below old leaves are
automatically stable under a literally fixed nonleaf numeric profile.
The argument does not prove that the second candidate is ordered,
role-preserving, satisfies target leaf range or future reserve,
nor that the SAME NUMERIC profile ever exists for a later w.
It is a finite conditional stability theorem, not a protected
relative extension, persistent leaf image or diary unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- For two FUNCTIONAL new-leaf generator tables with identical
nonleaf numeric images and identical old-stage mixed singleton
colour, a complete induced finite edge/nonedge table at the
first proposed leaf is inherited by the second.

Both functionality hypotheses are NECESSARY here: without
functionality of the second table its canonical chosen value at
the new leaf m need not equal its proposed target w. -/
theorem AdmissibleCofinalDiaryStage.candidate_full_induced_stable_of_old_cut_colour_and_profile
    {H K : Ordered3Graph Nat} {F f : Nat → Nat}
    {m v w : Nat}
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (hm : IsLeaf H m)
    (C : FiniteNewLeafCandidateCondition H K F m f v)
    (hFunctionalW : FiniteGeneratorTableFunctional
      (candidateNewLeafGeneratorTable H K m f w))
    (hSameNonleaf : ∀ u : Nat,
      u ∈ countableDiaryFiniteSupport H (m + 1) →
      u ≠ m →
      candidateNewLeafTableMap H K m f v u =
        candidateNewLeafTableMap H K m f w u)
    (hColour :
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) v =
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) w) :
    ∀ a b c : Nat,
      a ∈ countableDiaryFiniteSupport H (m + 1) →
      b ∈ countableDiaryFiniteSupport H (m + 1) →
      c ∈ countableDiaryFiniteSupport H (m + 1) →
      a < b → b < c →
      (H.edge a b c ↔
        K.edge
          (candidateNewLeafTableMap H K m f w a)
          (candidateNewLeafTableMap H K m f w b)
          (candidateNewLeafTableMap H K m f w c)) := by
  intro a b c ha hb hc hab hbc
  have hcM : c ≤ m :=
    countableDiaryFiniteSupport_succ_le_new_leaf H m c hm hc
  by_cases hcm : c = m
  · subst c
    have hTail :
        K.edge
          (candidateNewLeafTableMap H K m f v a)
          (candidateNewLeafTableMap H K m f v b) v ↔
        K.edge
          (candidateNewLeafTableMap H K m f w a)
          (candidateNewLeafTableMap H K m f w b) w :=
      P.candidate_terminal_edge_stable_of_old_cut_colour
        hm C.functional hSameNonleaf hColour
        a b ha hb hab hbc
        (C.ordered a b ha hb hab)
    have hmSelected :
        m ∈ countableDiaryLeafPrefix H (m + 1) :=
      (mem_countableDiaryLeafPrefix_iff H (m + 1) m).mpr
        ⟨hm.1, by omega, hm⟩
    have hCV :
        candidateNewLeafTableMap H K m f v m = v := by
      have h := C.chosen_selected_leaf m hmSelected
      simpa [candidateLeafImage] using h
    have hCW :
        candidateNewLeafTableMap H K m f w m = w := by
      change finiteGeneratorTableValue
        (candidateNewLeafGeneratorTable H K m f w) m = w
      have hRow :
          (m,candidateLeafImage f m w m) ∈
            candidateNewLeafGeneratorTable H K m f w :=
        finiteLeafGeneratorTable_leaf H K
          (countableDiaryLeafPrefix H (m + 1))
          (candidateLeafImage f m w) m hmSelected
      have h := finiteGeneratorTableValue_eq_of_mem
        (candidateNewLeafGeneratorTable H K m f w)
        hFunctionalW m (candidateLeafImage f m w m) hRow
      simpa [candidateLeafImage] using h
    have hInduced := C.induced_edge a b m ha hb hc hab hbc
    rw [hCV] at hInduced
    rw [hCW]
    exact hInduced.trans hTail
  · have hclt : c < m := by omega
    have haNe : a ≠ m := by omega
    have hbNe : b ≠ m := by omega
    have hcNe : c ≠ m := ne_of_lt hclt
    have hTarget :
        K.edge
          (candidateNewLeafTableMap H K m f v a)
          (candidateNewLeafTableMap H K m f v b)
          (candidateNewLeafTableMap H K m f v c) ↔
        K.edge
          (candidateNewLeafTableMap H K m f w a)
          (candidateNewLeafTableMap H K m f w b)
          (candidateNewLeafTableMap H K m f w c) := by
      rw [hSameNonleaf a ha haNe,
        hSameNonleaf b hb hbNe,
        hSameNonleaf c hc hcNe]
    exact (C.induced_edge a b c ha hb hc hab hbc).trans hTarget

end DiaryLeafPriority
end ThreeUniformDiaries
