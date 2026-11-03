import ThreeUniformDiaries.DiaryUpperBoundSharpFromCountableLeafModel
import ThreeUniformDiaries.DiaryExistenceFromShiftedSeed

/-!
# Track A: exact sharp upper bound from the ONE remaining shifted-seed V3 lemma

The only structural hypothesis of the sharp diary-leaf-model
upper bound is the existence of a countable full diary whose
true leaves contain an induced copy of the original universal U.

The verified Track B existence theorem constructs this full
diary from U provided the exact shifted three-marker seed
preserves and reflects the genuine LexEarlier comparison
between every old pair. We expose that SOLE numerical
hypothesis here and remove the abstract leaf-model assumption.

Thus the *upper bound* is proved conditional on one explicit
LexEarlier/V3 seed equivalence. It is independent of countable
diary unavoidability and of the matching lower degree theorem.
The statement does not assert the V3 equivalence is solved;
that outstanding task is Track B issue #1012 and the shifted
seed proof series.

The finite palette counts distinct genuine unmarked full
diary sources of A times |Aut(A)| EXACTLY ONCE.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph
open DiaryLeafPriority

/-- A sharp finite-colour upper bound for every countably
universal U satisfying the single explicit shifted-seed
lexicographic transport statement. No abstract diary-leaf
model or finite source ATR factorisation is an assumption:
both are built from the verified Track B existence conditional
and the Track A marked finite code construction.

No countable unavoidability or final Ramsey theorem is used. -/
theorem actualFiniteAuxRamsey_sharp_upper_of_shiftedSeedLex
    (G : GenericEnumerated3Graph)
    (U : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    (hLex : ∀ a b : Nat, a < b →
      (LexEarlier (shiftedDiarySeed U) (a+3) (b+3) ↔
        LexEarlier U a b))
    {a : Nat} (A : EnumNode a)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : (Fin a → Nat) → κ) :
    ∃ w : UnorderedEmbedding U U,
      ∃ palette : List κ,
        palette.length =
          (allGenuineUnmarkedDiarySources A).card *
          Fintype.card
            (FiniteHypergraphAut A.toOrdered3Graph a) ∧
        ∀ v : Fin a → Nat,
          IsInducedLabelledCopy A U v →
          χ (fun i => w (v i)) ∈ palette := by
  obtain ⟨H,D,e,hLeaf,_⟩ :=
    exists_countable_full_diary_with_exact_leaf_reduct_of_seed_lex
      U hLex
  exact actualFiniteAuxRamsey_sharp_upper_of_diaryLeafModel
    G U H D e.asUnordered hLeaf hUniversal A χ

end ATRFiniteDecoder
end ThreeUniformDiaries
