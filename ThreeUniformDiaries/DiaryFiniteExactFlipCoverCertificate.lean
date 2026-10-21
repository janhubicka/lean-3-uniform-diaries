import ThreeUniformDiaries.DiaryFiniteMultivaluedFlipAbsorption
import ThreeUniformDiaries.DiaryFiniteBoundedEmbeddingTable

/-!
# A genuinely finite table-based certificate for strong diary flip absorption

The exact multivalued covering criterion says that an absorber B is
precisely one for which each true target flip T has SOME source flip
P -> B whose T-pullback equals the prescribed unflipped A.

The entire condition can be reduced to FINITE domains:
* finite canonical Boolean edge codes of the real source flips;
* finite Boolean edge codes of the real target flips;
* bounded strictly increasing tables Fin n -> Fin k.

All total Nat -> Nat maps are eliminated by a canonical monotone tail
extension. The target pullback is unchanged by this normalisation,
because it only reads the first n source vertices.

This produces a *complete* finite covering certificate for any
fixed A,B, not merely a sufficient one-copy-per-flip permutation
test. It does NOT give a uniform bound on the absorbing target B,
and the classically filtered candidate finset is not by itself an
efficient executable decision algorithm.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A bounded induced ternary pullback only depends on the map's
finite restriction [0,n). The artificial infinite tails of two
maps are irrelevant to every source edge and nonedge. -/
theorem finiteDiaryPullbackGraph_eq_of_finite_prefix
    (T : Ordered3Graph Nat) (n : Nat)
    (f g : Nat → Nat)
    (hAgree : ∀ u : Nat, u < n → f u = g u) :
    finiteDiaryPullbackGraph T n f =
      finiteDiaryPullbackGraph T n g := by
  apply finiteDiary_graph_ext
  intro a b c
  constructor
  · intro h
    change a < b ∧ b < c ∧ c < n ∧
      T.edge (f a) (f b) (f c) at h
    obtain ⟨hab,hbc,hcn,hE⟩ := h
    have ha : a < n := by omega
    have hb : b < n := by omega
    have hNew : T.edge (g a) (g b) (g c) := by
      rw [← hAgree a ha,← hAgree b hb,← hAgree c hcn]
      exact hE
    exact ⟨hab,hbc,hcn,hNew⟩
  · intro h
    change a < b ∧ b < c ∧ c < n ∧
      T.edge (g a) (g b) (g c) at h
    obtain ⟨hab,hbc,hcn,hE⟩ := h
    have ha : a < n := by omega
    have hb : b < n := by omega
    have hOld : T.edge (f a) (f b) (f c) := by
      rw [hAgree a ha,hAgree b hb,hAgree c hcn]
      exact hE
    exact ⟨hab,hbc,hcn,hOld⟩

/-- Exact canonical flip absorption with ALL infinite embedding
witnesses replaced by genuinely finite, strictly increasing tables.
This is an equivalence, not a conditional feedback permutation. -/
theorem absorbsEveryTargetFlipInside_iff_finite_embedding_tables
    {A B : Ordered3Graph Nat} {n k : Nat}
    (DA : FiniteRoleDiaryBlock A n) :
    AbsorbsEveryTargetFlipInside A B n k ↔
      ∀ tcode : FiniteDiaryEdgeCode k,
        tcode ∈ finiteSourceFlipCodes B k →
        ∃ scode : FiniteDiaryEdgeCode n,
          scode ∈ finiteCanonicalSourceFlipCodes A n ∧
          ∃ g : Fin n → Fin k,
            StrictMono g ∧
            FiniteBoundedMeetEmbedding
              (finiteDiaryCodeGraph n scode) B n k
              (extendFiniteBoundedMap n k g) ∧
            finiteDiaryPullbackGraph
              (finiteDiaryCodeGraph k tcode) n
              (extendFiniteBoundedMap n k g) = A := by
  constructor
  · intro hAbs tcode ht
    obtain ⟨scode,hc,f,E,hPull⟩ :=
      (absorbsEveryTargetFlipInside_iff_finite_multivalued_flip_codes
        DA).mp hAbs tcode ht
    obtain ⟨g,hg,hEg,hAgree⟩ :=
      E.exists_finite_table DA.prediary.frame.length_ge_three
    refine ⟨scode,hc,g,hg,hEg,?_⟩
    exact (finiteDiaryPullbackGraph_eq_of_finite_prefix
      (finiteDiaryCodeGraph k tcode) n
      (extendFiniteBoundedMap n k g) f hAgree).trans hPull
  · intro hCodes
    apply (absorbsEveryTargetFlipInside_iff_finite_multivalued_flip_codes
      DA).mpr
    intro tcode ht
    obtain ⟨scode,hc,g,_hg,hE,hPull⟩ := hCodes tcode ht
    exact ⟨scode,hc,extendFiniteBoundedMap n k g,hE,hPull⟩

/-- The FINITE set of all genuine canonical-source-flip and
bounded protected embedding-table pairs inside the original
target B. This retains ALL maps, not one arbitrarily selected
map for each source flip. The definition is classical; it is a
mathematical finite search space, not a performance promise. -/
noncomputable def finiteCanonicalFlipEmbeddingTables
    (A B : Ordered3Graph Nat) (n k : Nat) :
    Finset (FiniteDiaryEdgeCode n × (Fin n → Fin k)) := by
  classical
  exact Finset.univ.filter (fun p =>
    p.1 ∈ finiteCanonicalSourceFlipCodes A n ∧
    StrictMono p.2 ∧
    FiniteBoundedMeetEmbedding
      (finiteDiaryCodeGraph n p.1) B n k
      (extendFiniteBoundedMap n k p.2))

/-- Membership in the finite candidate table set means precisely
a genuine canonical source flip and an honest protected copy of
that flip inside B, with no fictitious free Boolean controls. -/
theorem mem_finiteCanonicalFlipEmbeddingTables_iff
    (A B : Ordered3Graph Nat) (n k : Nat)
    (p : FiniteDiaryEdgeCode n × (Fin n → Fin k)) :
    p ∈ finiteCanonicalFlipEmbeddingTables A B n k ↔
      p.1 ∈ finiteCanonicalSourceFlipCodes A n ∧
      StrictMono p.2 ∧
      FiniteBoundedMeetEmbedding
        (finiteDiaryCodeGraph n p.1) B n k
        (extendFiniteBoundedMap n k p.2) := by
  classical
  simp [finiteCanonicalFlipEmbeddingTables]

/-- THE EXACT FINITE COVER CERTIFICATE:
B absorbs A under ALL genuine target flips if and only if each
target-flip Boolean code is hit by at least one member of the
finite set of protected source-flip embedding tables.

No global feedback injectivity, common rank or preselected
embedding family is required. Existence of some absorber for
arbitrary A remains the open geometric theorem. -/
theorem absorbsEveryTargetFlipInside_iff_finite_table_cover
    {A B : Ordered3Graph Nat} {n k : Nat}
    (DA : FiniteRoleDiaryBlock A n) :
    AbsorbsEveryTargetFlipInside A B n k ↔
      ∀ tcode : FiniteDiaryEdgeCode k,
        tcode ∈ finiteSourceFlipCodes B k →
        ∃ p : FiniteDiaryEdgeCode n × (Fin n → Fin k),
          p ∈ finiteCanonicalFlipEmbeddingTables A B n k ∧
          finiteDiaryPullbackGraph
            (finiteDiaryCodeGraph k tcode) n
            (extendFiniteBoundedMap n k p.2) = A := by
  rw [absorbsEveryTargetFlipInside_iff_finite_embedding_tables DA]
  constructor
  · intro h tcode ht
    obtain ⟨scode,hc,g,hg,hE,hPull⟩ := h tcode ht
    exact ⟨(scode,g),
      (mem_finiteCanonicalFlipEmbeddingTables_iff
        A B n k (scode,g)).mpr ⟨hc,hg,hE⟩,
      hPull⟩
  · intro h tcode ht
    obtain ⟨p,hp,hPull⟩ := h tcode ht
    have hValid :=
      (mem_finiteCanonicalFlipEmbeddingTables_iff
        A B n k p).mp hp
    exact ⟨p.1,hValid.1,p.2,hValid.2.1,hValid.2.2,hPull⟩

end DiaryLeafPriority
end ThreeUniformDiaries
