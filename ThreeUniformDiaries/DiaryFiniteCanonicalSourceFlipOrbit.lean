import ThreeUniformDiaries.DiaryFiniteSourceFlipCodeOrbit

/-!
# Canonical rather than redundant Boolean codes for actual source flips

The raw Boolean tables on (Fin n)^3 contain irrelevant entries on
non-increasing triples. Distinct raw tables can represent exactly
the same diary. Feedback injectivity therefore MUST NOT be posed
on all raw members of finiteSourceFlipCodes.

A code is canonical when encoding its decoded graph produces the
same table. Canonical codes are in one-to-one correspondence with
genuine finite diary flip graphs. We define the corrected finite
source-flip orbit by filtering for this normalization condition.

All proofs are by faithful finite graph reconstruction; no
independence of one-split and two-split controls is assumed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The raw edge table has no irrelevant noncanonical bits. -/
def IsCanonicalFiniteDiaryEdgeCode
    (n : Nat) (code : FiniteDiaryEdgeCode n) : Prop :=
  finiteDiaryEdgeCode (finiteDiaryCodeGraph n code) n = code

/-- TRUE finite orbit of genuine source diary flips represented
by canonical edge tables, one code per actual finite graph. -/
noncomputable def finiteCanonicalSourceFlipCodes
    (A : Ordered3Graph Nat) (n : Nat) :
    Finset (FiniteDiaryEdgeCode n) := by
  classical
  exact (finiteSourceFlipCodes A n).filter
    (fun code => IsCanonicalFiniteDiaryEdgeCode n code)

/-- Canonical flip membership combines true flip validity with
absence of spurious bits on repeated/unordered triples. -/
theorem mem_finiteCanonicalSourceFlipCodes_iff
    (A : Ordered3Graph Nat) (n : Nat)
    (code : FiniteDiaryEdgeCode n) :
    code ∈ finiteCanonicalSourceFlipCodes A n ↔
      code ∈ finiteSourceFlipCodes A n ∧
        IsCanonicalFiniteDiaryEdgeCode n code := by
  classical
  simp [finiteCanonicalSourceFlipCodes]

/-- The baseline code of every genuine finite diary is canonical. -/
theorem finiteCanonicalSourceFlipCodes_baseline_mem
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n) :
    finiteDiaryEdgeCode A n ∈
      finiteCanonicalSourceFlipCodes A n := by
  apply (mem_finiteCanonicalSourceFlipCodes_iff A n _).mpr
  refine ⟨finiteSourceFlipCodes_baseline_mem DA, ?_⟩
  unfold IsCanonicalFiniteDiaryEdgeCode
  rw [finiteDiaryCodeGraph_reconstruct A n DA.prediary.frame]

/-- Every genuine diary flip has its literal canonical finite
edge table in the new family, reconstructing exactly the flip. -/
theorem finiteCanonicalSourceFlipCodes_complete
    {A P : Ordered3Graph Nat} {n : Nat}
    (F : FiniteDiaryFlip A P n) :
    ∃ code : FiniteDiaryEdgeCode n,
      code ∈ finiteCanonicalSourceFlipCodes A n ∧
      finiteDiaryCodeGraph n code = P := by
  let code := finiteDiaryEdgeCode P n
  have hRecon : finiteDiaryCodeGraph n code = P :=
    finiteDiaryCodeGraph_reconstruct
      P n F.target_diary.prediary.frame
  refine ⟨code, ?_, hRecon⟩
  apply (mem_finiteCanonicalSourceFlipCodes_iff A n code).mpr
  constructor
  · exact (mem_finiteSourceFlipCodes_iff A n code).mpr (by
      rw [hRecon]
      exact F)
  · unfold IsCanonicalFiniteDiaryEdgeCode
    rw [hRecon]

/-- Decoding is INJECTIVE on the canonical source-flip orbit.
This precisely removes the duplicate-encoding obstruction. -/
theorem finiteCanonicalSourceFlipCodes_decode_injective
    (A : Ordered3Graph Nat) (n : Nat)
    (c d : FiniteDiaryEdgeCode n)
    (hc : c ∈ finiteCanonicalSourceFlipCodes A n)
    (hd : d ∈ finiteCanonicalSourceFlipCodes A n)
    (hGraph : finiteDiaryCodeGraph n c =
      finiteDiaryCodeGraph n d) : c = d := by
  have hcNormal :
      finiteDiaryEdgeCode (finiteDiaryCodeGraph n c) n = c :=
    ((mem_finiteCanonicalSourceFlipCodes_iff A n c).mp hc).2
  have hdNormal :
      finiteDiaryEdgeCode (finiteDiaryCodeGraph n d) n = d :=
    ((mem_finiteCanonicalSourceFlipCodes_iff A n d).mp hd).2
  calc
    c = finiteDiaryEdgeCode (finiteDiaryCodeGraph n c) n :=
      hcNormal.symm
    _ = finiteDiaryEdgeCode (finiteDiaryCodeGraph n d) n :=
      congrArg (fun H : Ordered3Graph Nat =>
        finiteDiaryEdgeCode H n) hGraph
    _ = d := hdNormal

/-- A raw source-flip code normalizes to a canonical source-flip
code without changing the represented finite diary. -/
theorem finiteSourceFlipCode_normalized_mem
    (A : Ordered3Graph Nat) (n : Nat)
    (c : FiniteDiaryEdgeCode n)
    (hc : c ∈ finiteSourceFlipCodes A n) :
    finiteDiaryEdgeCode (finiteDiaryCodeGraph n c) n ∈
      finiteCanonicalSourceFlipCodes A n := by
  let P := finiteDiaryCodeGraph n c
  have FP : FiniteDiaryFlip A P n :=
    (mem_finiteSourceFlipCodes_iff A n c).mp hc
  have hRecon :
      finiteDiaryCodeGraph n (finiteDiaryEdgeCode P n) = P :=
    finiteDiaryCodeGraph_reconstruct
      P n FP.target_diary.prediary.frame
  apply (mem_finiteCanonicalSourceFlipCodes_iff A n _).mpr
  constructor
  · exact (mem_finiteSourceFlipCodes_iff A n _).mpr (by
      rw [hRecon]
      exact FP)
  · unfold IsCanonicalFiniteDiaryEdgeCode
    change finiteDiaryEdgeCode
        (finiteDiaryCodeGraph n (finiteDiaryEdgeCode P n)) n =
      finiteDiaryEdgeCode P n
    rw [hRecon]

/-- Normalization gives a well-defined retraction from raw codes
of realisable flips to their unique canonical representatives. -/
noncomputable def canonicalSourceFlipCodeOfRaw
    (A : Ordered3Graph Nat) (n : Nat)
    (c : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteSourceFlipCodes A n}) :
    {code : FiniteDiaryEdgeCode n //
      code ∈ finiteCanonicalSourceFlipCodes A n} :=
  ⟨finiteDiaryEdgeCode (finiteDiaryCodeGraph n c.val) n,
   finiteSourceFlipCode_normalized_mem A n c.val c.property⟩

/-- Normalization does nothing on an already canonical code. -/
theorem canonicalSourceFlipCodeOfRaw_fixed
    (A : Ordered3Graph Nat) (n : Nat)
    (c : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteCanonicalSourceFlipCodes A n}) :
    (canonicalSourceFlipCodeOfRaw A n
      ⟨c.val,
        ((mem_finiteCanonicalSourceFlipCodes_iff A n c.val).mp
          c.property).1⟩).val = c.val := by
  exact ((mem_finiteCanonicalSourceFlipCodes_iff A n
    c.val).mp c.property).2

/-- The canonical orbit is invariant when the baseline is
replaced by any genuine finite flip of that baseline. -/
theorem finiteCanonicalSourceFlipCodes_eq_of_flip
    {A P : Ordered3Graph Nat} {n : Nat}
    (F : FiniteDiaryFlip A P n) :
    finiteCanonicalSourceFlipCodes A n =
      finiteCanonicalSourceFlipCodes P n := by
  unfold finiteCanonicalSourceFlipCodes
  rw [finiteSourceFlipCodes_eq_of_flip F]

end DiaryLeafPriority
end ThreeUniformDiaries
