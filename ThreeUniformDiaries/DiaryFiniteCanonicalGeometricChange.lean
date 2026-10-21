import ThreeUniformDiaries.DiaryFiniteCanonicalNonleafCausality
import ThreeUniformDiaries.DiaryFiniteCanonicalLiteralEdgeSeparation

/-!
# Geometric edge-change bits behind canonical flip feedback

Let P be a genuine canonical source flip represented by code c and
f_c a selected fully protected copy in a finite diary B. For any
target flip T of B, the canonical source feedback bit at a genuine
increasing source triple is precisely the incidence of the T-image
under f_c. The ORIGINAL input source code bit is the incidence of
the B-image of the SAME triple, since f_c is induced.

The feedback XOR correction is consequently EXACTLY the Boolean
difference of B- and T-incidence at the triple of image vertices.
This identity is unconditional and uses no abstract causality.

It yields a more geometric sufficient condition: for each genuine
increasing source triple with at least one nonleaf coordinate, the
edge-change bit seen along f_c is determined by only strictly
lower-ranked genuine source edge bits of c. If this holds for every
target flip, the verified finite-orbit argument gives strong
absorption. Existence of such a chosen copy family remains OPEN.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The actual bit changed by the target flip T relative to B
at one ordered triple. This definition makes no claim that B
and T differ only on a specific type of source triple. -/
noncomputable def finiteTargetFlipChangeBit
    (B T : Ordered3Graph Nat) (x y z : Nat) : Bool :=
  Bool.xor (finiteTargetEdgeBit T x y z)
    (finiteTargetEdgeBit B x y z)

/-- For each source canonical flip code, the corresponding genuine
increasing edge bit equals the ORIGINAL target B edge bit at the
chosen fully protected image of that source triple. -/
theorem canonicalChosenCopy_baseline_edge_bit
    (A B : Ordered3Graph Nat) (n k : Nat)
    (DB : FiniteRoleDiaryBlock B k)
    (hCopies : ∀ code : FiniteDiaryEdgeCode n,
      code ∈ finiteCanonicalSourceFlipCodes A n →
      ∃ f : Nat → Nat,
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n code) B n k f)
    (c : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteCanonicalSourceFlipCodes A n})
    (i j z : Fin n) (hij : i < j) (hjz : j < z) :
    c.val i j z =
      finiteTargetEdgeBit B
        ((chosenCanonicalSourceFlipMap A B n k hCopies c) i.val)
        ((chosenCanonicalSourceFlipMap A B n k hCopies c) j.val)
        ((chosenCanonicalSourceFlipMap A B n k hCopies c) z.val) := by
  let f := chosenCanonicalSourceFlipMap A B n k hCopies c
  let F : FiniteDiaryFlip B B k := FiniteDiaryFlip.refl DB
  have hId :
      (realizedCanonicalSourceFlipFeedback
        A B B n k hCopies F c).val = c.val :=
    congrArg Subtype.val
      (realizedCanonicalSourceFlipFeedback_refl_eq
        A B n k DB hCopies c)
  have hVal :
      (realizedCanonicalSourceFlipFeedback
        A B B n k hCopies F c).val =
          finiteDiaryEdgeCode (finiteDiaryPullbackGraph B n f) n :=
    realizedCanonicalSourceFlipFeedback_val A B B n k hCopies F c
  have hSource : c.val =
      finiteDiaryEdgeCode (finiteDiaryPullbackGraph B n f) n :=
    hId.symm.trans hVal
  have hAt := congrFun (congrFun (congrFun hSource i) j) z
  exact hAt.trans
    (finiteDiaryPullback_edgeCode_increasing
      B n f i j z hij hjz)

/-- Under an arbitrary genuine target flip T, the actual
feedback edge bit is the T-incidence at the SAME selected image. -/
theorem canonicalChosenCopy_flipped_edge_bit
    (A B T : Ordered3Graph Nat) (n k : Nat)
    (hCopies : ∀ code : FiniteDiaryEdgeCode n,
      code ∈ finiteCanonicalSourceFlipCodes A n →
      ∃ f : Nat → Nat,
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n code) B n k f)
    (FT : FiniteDiaryFlip B T k)
    (c : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteCanonicalSourceFlipCodes A n})
    (i j z : Fin n) (hij : i < j) (hjz : j < z) :
    (realizedCanonicalSourceFlipFeedback
        A B T n k hCopies FT c).val i j z =
      finiteTargetEdgeBit T
        ((chosenCanonicalSourceFlipMap A B n k hCopies c) i.val)
        ((chosenCanonicalSourceFlipMap A B n k hCopies c) j.val)
        ((chosenCanonicalSourceFlipMap A B n k hCopies c) z.val) := by
  let f := chosenCanonicalSourceFlipMap A B n k hCopies c
  have hVal := realizedCanonicalSourceFlipFeedback_val
    A B T n k hCopies FT c
  have hAt := congrFun (congrFun (congrFun hVal i) j) z
  exact hAt.trans
    (finiteDiaryPullback_edgeCode_increasing
      T n f i j z hij hjz)

/-- The literal change bit of T relative to B at the
selected image of an increasing source triple. -/
noncomputable def canonicalChosenCopyGeometricChange
    (A B T : Ordered3Graph Nat) (n k : Nat)
    (hCopies : ∀ code : FiniteDiaryEdgeCode n,
      code ∈ finiteCanonicalSourceFlipCodes A n →
      ∃ f : Nat → Nat,
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n code) B n k f)
    (c : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteCanonicalSourceFlipCodes A n})
    (i j z : Fin n) : Bool :=
  finiteTargetFlipChangeBit B T
    ((chosenCanonicalSourceFlipMap A B n k hCopies c) i.val)
    ((chosenCanonicalSourceFlipMap A B n k hCopies c) j.val)
    ((chosenCanonicalSourceFlipMap A B n k hCopies c) z.val)

/-- Fundamental unconditional identity: canonical feedback XOR
correction = the B-to-T edge-change bit at the selected copy's
actual triple of target vertices. No geometric hypothesis. -/
theorem canonicalFeedback_correction_eq_geometricChange
    (A B T : Ordered3Graph Nat) (n k : Nat)
    (hCopies : ∀ code : FiniteDiaryEdgeCode n,
      code ∈ finiteCanonicalSourceFlipCodes A n →
      ∃ f : Nat → Nat,
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n code) B n k f)
    (FT : FiniteDiaryFlip B T k)
    (c : {code : FiniteDiaryEdgeCode n //
      code ∈ finiteCanonicalSourceFlipCodes A n})
    (i j z : Fin n) (hij : i < j) (hjz : j < z) :
    Bool.xor
      ((realizedCanonicalSourceFlipFeedback
        A B T n k hCopies FT c).val i j z)
      (c.val i j z) =
      canonicalChosenCopyGeometricChange
        A B T n k hCopies c i j z := by
  have hNew := canonicalChosenCopy_flipped_edge_bit
    A B T n k hCopies FT c i j z hij hjz
  have hOld := canonicalChosenCopy_baseline_edge_bit
    A B n k FT.source_diary hCopies c i j z hij hjz
  change Bool.xor
      ((realizedCanonicalSourceFlipFeedback
        A B T n k hCopies FT c).val i j z)
      (c.val i j z) =
      finiteTargetFlipChangeBit B T
        ((chosenCanonicalSourceFlipMap A B n k hCopies c) i.val)
        ((chosenCanonicalSourceFlipMap A B n k hCopies c) j.val)
        ((chosenCanonicalSourceFlipMap A B n k hCopies c) z.val)
  unfold finiteTargetFlipChangeBit
  rw [hNew,hOld]

/-- A single source triple rank is sufficient for complete
bounded absorption if the ACTUAL B-to-T edge changes on chosen
copies agree whenever canonical source codes agree on lower-ranked
genuine increasing triples. Only nonleaf source triples matter. -/
theorem absorbsEveryTargetFlipInside_of_geometricChange_ranked
    (A B : Ordered3Graph Nat) (n k : Nat)
    (DA : FiniteRoleDiaryBlock A n)
    (hCopies : ∀ code : FiniteDiaryEdgeCode n,
      code ∈ finiteCanonicalSourceFlipCodes A n →
      ∃ f : Nat → Nat,
        FiniteBoundedMeetEmbedding
          (finiteDiaryCodeGraph n code) B n k f)
    (rank : Fin n → Fin n → Fin n → Nat)
    (hGeometric : ∀ (T : Ordered3Graph Nat)
      (FT : FiniteDiaryFlip B T k)
      (c d : {code : FiniteDiaryEdgeCode n //
        code ∈ finiteCanonicalSourceFlipCodes A n})
      (i j z : Fin n),
      i < j → j < z →
      (¬ IsLeaf A i.val ∨ ¬ IsLeaf A j.val ∨
        ¬ IsLeaf A z.val) →
      (∀ a b t : Fin n,
        a < b → b < t → rank a b t < rank i j z →
        c.val a b t = d.val a b t) →
      canonicalChosenCopyGeometricChange
        A B T n k hCopies c i j z =
      canonicalChosenCopyGeometricChange
        A B T n k hCopies d i j z) :
    AbsorbsEveryTargetFlipInside A B n k := by
  apply absorbsEveryTargetFlipInside_of_nonleaf_ranked_causality
    A B n k DA hCopies rank
  intro T FT c d i j z hij hjz hNonleaf hBefore
  calc
    Bool.xor
      ((realizedCanonicalSourceFlipFeedback
        A B T n k hCopies FT c).val i j z)
      (c.val i j z) =
        canonicalChosenCopyGeometricChange
          A B T n k hCopies c i j z :=
      canonicalFeedback_correction_eq_geometricChange
        A B T n k hCopies FT c i j z hij hjz
    _ = canonicalChosenCopyGeometricChange
          A B T n k hCopies d i j z :=
      hGeometric T FT c d i j z hij hjz hNonleaf hBefore
    _ = Bool.xor
      ((realizedCanonicalSourceFlipFeedback
        A B T n k hCopies FT d).val i j z)
      (d.val i j z) :=
      (canonicalFeedback_correction_eq_geometricChange
        A B T n k hCopies FT d i j z hij hjz).symm

end DiaryLeafPriority
end ThreeUniformDiaries
