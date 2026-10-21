import ThreeUniformDiaries.DiaryFiniteExactFlipCoverCertificate
import ThreeUniformDiaries.DiaryFiniteCanonicalE2E3Separation
import ThreeUniformDiaries.DiaryFiniteFlipTransitivity
import ThreeUniformDiaries.DiaryFinitePullbackProtectedEmbedding

/-!
# E2/E3 coordinates completely determine genuine finite diary flips

The finite canonical source-flip orbit is not a freely chosen Boolean
cube. Nevertheless, the already verified E2/E3 edge-separation theorem
shows its restriction to the TRUE one-split and two-split incidences
is faithful.

This module promotes that separation to an exact equality criterion:
two genuine flips of a fixed source diary coincide precisely if they
agree at ALL E2 and E3 source coordinates.

Combined with the verified canonical geometric pullback, a map of
some genuine source flip into B survives as the ORIGINAL source A
in a target flip T iff the target incidences at the images of those
E2/E3 coordinates equal the baseline source incidences.

This permits a complete finite absorption certificate checking only
genuine E2/E3 coordinates rather than every source triple. No split
control is assumed independent; no absorbing target is constructed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Equality of two genuinely flipped finite diaries follows from
their agreement on E2/E3 incidences. E4 Devlin markers are dependent,
and E1 roles/E5 leaf-only edges are invariant under actual flips. -/
theorem FiniteDiaryFlip.eq_of_E2E3_agreement
    {A P : Ordered3Graph Nat} {n : Nat}
    (F : FiniteDiaryFlip A P n)
    (hAgree : ∀ i j z : Fin n,
      i < j → j < z →
      IsFiniteFlipE2OrE3Edge A i.val j.val z.val →
      (P.edge i.val j.val z.val ↔ A.edge i.val j.val z.val)) :
    P = A := by
  classical
  let ac : FiniteDiaryEdgeCode n := finiteDiaryEdgeCode A n
  let pc : FiniteDiaryEdgeCode n := finiteDiaryEdgeCode P n
  have ha : ac ∈ finiteCanonicalSourceFlipCodes A n :=
    finiteCanonicalSourceFlipCodes_baseline_mem F.source_diary
  have hp : pc ∈ finiteCanonicalSourceFlipCodes A n := by
    apply (mem_finiteCanonicalSourceFlipCodes_iff A n pc).mpr
    constructor
    · apply (mem_finiteSourceFlipCodes_iff A n pc).mpr
      change FiniteDiaryFlip A (finiteDiaryCodeGraph n pc) n
      rw [finiteDiaryCodeGraph_reconstruct P n
        F.target_diary.prediary.frame]
      exact F
    · unfold IsCanonicalFiniteDiaryEdgeCode
      exact finiteDiaryCodeGraph_reconstruct P n
        F.target_diary.prediary.frame ▸ rfl
  by_contra hne
  have hcodeNe : ac ≠ pc := by
    intro heq
    have hA := finiteDiaryCodeGraph_reconstruct A n
      F.source_diary.prediary.frame
    have hP := finiteDiaryCodeGraph_reconstruct P n
      F.target_diary.prediary.frame
    have hAP : A = P := by
      calc
        A = finiteDiaryCodeGraph n ac := hA.symm
        _ = finiteDiaryCodeGraph n pc :=
          congrArg (finiteDiaryCodeGraph n) heq
        _ = P := hP
    exact hne hAP.symm
  obtain ⟨i,j,z,hij,hjz,hShape,hDiff⟩ :=
    canonical_source_flips_ne_E2_or_E3_edge_witness
      A n ac pc ha hp hcodeNe
  have hEdge := hAgree i j z hij hjz hShape
  have hSame : ac i j z = pc i j z := by
    classical
    simp [ac,pc,finiteDiaryEdgeCode,hEdge]
  exact hDiff hSame

/-- The equality test can be applied on either side: among actual
source flips, all E2/E3 edge incidences are a COMPLETE invariant. -/
theorem FiniteDiaryFlip.eq_iff_E2E3_agreement
    {A P : Ordered3Graph Nat} {n : Nat}
    (F : FiniteDiaryFlip A P n) :
    P = A ↔ ∀ i j z : Fin n,
      i < j → j < z →
      IsFiniteFlipE2OrE3Edge A i.val j.val z.val →
      (P.edge i.val j.val z.val ↔ A.edge i.val j.val z.val) := by
  constructor
  · intro h
    subst P
    intro i j z hij hjz hShape
    exact Iff.rfl
  · exact F.eq_of_E2E3_agreement

/-- The canonical pullback from a protected source-flip copy is
the baseline A iff the target flip has exactly A's E2/E3 bits
at the chosen copy's genuine source coordinates.

All mixed meet transport and E4 reconstruction are consequences
of the existing finite induced-pullback machinery. -/
theorem finiteDiaryPullbackGraph_eq_baseline_iff_E2E3
    {A P B T : Ordered3Graph Nat} {n k : Nat}
    {f : Nat → Nat}
    (FP : FiniteDiaryFlip A P n)
    (EP : FiniteBoundedMeetEmbedding P B n k f)
    (FT : FiniteDiaryFlip B T k) :
    finiteDiaryPullbackGraph T n f = A ↔
      ∀ i j z : Fin n,
        i < j → j < z →
        IsFiniteFlipE2OrE3Edge A i.val j.val z.val →
        (T.edge (f i.val) (f j.val) (f z.val) ↔
          A.edge i.val j.val z.val) := by
  let Q := finiteDiaryPullbackGraph T n f
  have FQ : FiniteDiaryFlip P Q n :=
    finiteDiaryPullbackGraph_is_sourceFlip
      FP.target_diary EP.toMeetEmbedding EP.image_bound FT
  have FAQ : FiniteDiaryFlip A Q n := FP.trans FQ
  constructor
  · intro hEq i j z hij hjz _hShape
    have hBit := finiteDiaryPullbackGraph_edge_iff
      T n f i.val j.val z.val hij hjz z.isLt
    change Q.edge i.val j.val z.val ↔
      T.edge (f i.val) (f j.val) (f z.val) at hBit
    have hQA : Q = A := hEq
    rw [hQA] at hBit
    exact hBit.symm
  · intro hAgree
    apply FAQ.eq_of_E2E3_agreement
    intro i j z hij hjz hShape
    exact (finiteDiaryPullbackGraph_edge_iff
      T n f i.val j.val z.val hij hjz z.isLt).trans
        (hAgree i j z hij hjz hShape)

/-- The EXACT finite, multivalued target-flip cover certificate
needs to check ONLY the genuine E2/E3 incidences of the source.

The quantifiers range over finite true source-flip/target-flip
code orbits and finite bounded embedding tables. The certificate
is necessary AND sufficient for strong finite absorption for a
given A and B. Existence of such a B remains OPEN. -/
theorem absorbsEveryTargetFlipInside_iff_E2E3_finite_table_cover
    {A B : Ordered3Graph Nat} {n k : Nat}
    (DA : FiniteRoleDiaryBlock A n) :
    AbsorbsEveryTargetFlipInside A B n k ↔
      ∀ tcode : FiniteDiaryEdgeCode k,
        tcode ∈ finiteSourceFlipCodes B k →
        ∃ p : FiniteDiaryEdgeCode n × (Fin n → Fin k),
          p ∈ finiteCanonicalFlipEmbeddingTables A B n k ∧
          ∀ i j z : Fin n,
            i < j → j < z →
            IsFiniteFlipE2OrE3Edge A i.val j.val z.val →
            ((finiteDiaryCodeGraph k tcode).edge
              (extendFiniteBoundedMap n k p.2 i.val)
              (extendFiniteBoundedMap n k p.2 j.val)
              (extendFiniteBoundedMap n k p.2 z.val) ↔
              A.edge i.val j.val z.val) := by
  rw [absorbsEveryTargetFlipInside_iff_finite_table_cover DA]
  constructor
  · intro hCover tcode ht
    obtain ⟨p,hp,hPull⟩ := hCover tcode ht
    have hCandidate :=
      (mem_finiteCanonicalFlipEmbeddingTables_iff A B n k p).mp hp
    have hRaw : p.1 ∈ finiteSourceFlipCodes A n :=
      ((mem_finiteCanonicalSourceFlipCodes_iff A n p.1).mp
        hCandidate.1).1
    have FP : FiniteDiaryFlip A
      (finiteDiaryCodeGraph n p.1) n :=
      (mem_finiteSourceFlipCodes_iff A n p.1).mp hRaw
    have FT : FiniteDiaryFlip B
      (finiteDiaryCodeGraph k tcode) k :=
      (mem_finiteSourceFlipCodes_iff B k tcode).mp ht
    exact ⟨p,hp,
      (finiteDiaryPullbackGraph_eq_baseline_iff_E2E3
        FP hCandidate.2.2 FT).mp hPull⟩
  · intro hCover tcode ht
    obtain ⟨p,hp,hBits⟩ := hCover tcode ht
    have hCandidate :=
      (mem_finiteCanonicalFlipEmbeddingTables_iff A B n k p).mp hp
    have hRaw : p.1 ∈ finiteSourceFlipCodes A n :=
      ((mem_finiteCanonicalSourceFlipCodes_iff A n p.1).mp
        hCandidate.1).1
    have FP : FiniteDiaryFlip A
      (finiteDiaryCodeGraph n p.1) n :=
      (mem_finiteSourceFlipCodes_iff A n p.1).mp hRaw
    have FT : FiniteDiaryFlip B
      (finiteDiaryCodeGraph k tcode) k :=
      (mem_finiteSourceFlipCodes_iff B k tcode).mp ht
    exact ⟨p,hp,
      (finiteDiaryPullbackGraph_eq_baseline_iff_E2E3
        FP hCandidate.2.2 FT).mpr hBits⟩

end DiaryLeafPriority
end ThreeUniformDiaries
