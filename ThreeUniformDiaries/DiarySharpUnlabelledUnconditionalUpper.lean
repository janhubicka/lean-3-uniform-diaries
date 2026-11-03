import ThreeUniformDiaries.DiaryUpperBoundSharpUnconditional
import ThreeUniformDiaries.DiarySharpUnlabelledConditionalUpper
import ThreeUniformDiaries.DiaryUpperBoundGenuineLeafFactorisation
import ThreeUniformDiaries.DiaryUpperBoundUnorderedCopyModelTransfer

/-!
# Track A: unconditional sharp palette for unlabelled copies

The merged sharp labelled upper theorem gives one palette entry per genuine
marked full diary, or |Aut(A)| times the underlying unmarked source count.
For colourings of UNLABELLED A-copies (finite vertex sets) that multiplier
is unnecessary. The verified shape-indexed finite ATR Ramsey theorem and
its genuine marked-to-unmarked factorisation interface already yield
one colour per complete unmarked diary source, provided every labelled
copy factors through an actual finite marked ATR code.

We discharge this last conditional factorisation by combining:
* unconditional existence of a countable full diary whose entire leaf
  reduct is the chosen countably universal hypergraph;
* the genuine global auxiliary embedding of that diary into the generic G;
* unordered labelled-copy transport and the exact finite leaf-generated
  genuine marked ATR code theorem;
* a generic-to-universal unordered embedding from countable universality.

The conclusion concerns unordered induced self-embeddings U → U and finite
vertex sets, not a diary self-embedding and not the matching lower bound.
There is no V3 assumption, countable unavoidability, or final diary
Ramsey theorem in this proof.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- A sharp upper palette for unlabelled finite copies: at most the
number of genuine unmarked full diary source shapes. In particular,
there is NO factor |Aut(A)| in this unlabelled-copy bound. -/
theorem actualFiniteAuxRamsey_sharp_unlabelled_upper
    (G : GenericEnumerated3Graph)
    (U : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    {a : Nat} (A : EnumNode a)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : Finset Nat → κ) :
    ∃ w : UnorderedEmbedding U U,
      ∃ palette : List κ,
        palette.length = (allGenuineUnmarkedDiarySources A).card ∧
        ∀ v : Fin a → Nat,
          IsInducedLabelledCopy A U v →
          χ ((Finset.univ : Finset (Fin a)).image
            (fun i => w (v i))) ∈ palette := by
  classical
  obtain ⟨H, D, e, hLeaf, _⟩ :=
    exists_countable_full_diary_with_exact_leaf_reduct U
  obtain ⟨η, hη, _, _⟩ :=
    exists_auxTypeRespecting_embedding_fix_two G H
  let phi : UnorderedEmbedding U G.graph :=
    (η.asUnordered).comp e.asUnordered
  let psi : UnorderedEmbedding G.graph U :=
    Classical.choice (hUniversal G.graph)
  have hFactors :
      ∀ v : Fin a → Nat,
        IsInducedLabelledCopy A U v →
        ∃ T ∈ allGenuineMarkedDiaryShapes A,
          ∃ code : T.source.Code G,
            ∀ i : Fin a, phi (v i) =
              code.image (T.marked i) := by
    intro v hv
    have hLeaves :
        ∀ i : Fin a, IsLeaf H (e (v i)) := by
      intro i
      exact hLeaf (v i)
    have hCopy :
        IsFiniteLabelledCopy A.toOrdered3Graph G.graph a
          (fun i => η (e (v i))) :=
      finiteLabelledCopy_after_diaryLeafAndGeneric
        G U H A e.asUnordered η v hv
    obtain ⟨T, hT, code, hCode⟩ :=
      finiteDiaryLeafTuple_genuineMarkedGenericFactorisation
        G H D η hη A (fun i => e (v i))
        hLeaves hCopy
    refine ⟨T, hT, code, ?_⟩
    intro i
    change η (e (v i)) = code.image (T.marked i)
    exact hCode i
  exact actualFiniteAuxRamsey_direct_unlabelled_genuineDiaryCount
    G U A phi psi χ hFactors

end ATRFiniteDecoder
end ThreeUniformDiaries
