import ThreeUniformDiaries.DiaryCanonicalMarkedSubcopyComposition

/-!
# Coherent finite colours determine finite relational expansion profiles

This is the abstract, diary-INDEPENDENT kernel lemma behind the
Hubicka--Zucker big Ramsey structure construction. Given a coherent
family of finite embedding colourings, introduce one relation symbol
per finite enumerated source A and colour d. The relation holds of
a tuple exactly if the tuple is a genuine induced A-copy of colour d.

The crucial point is that a FULL finite induced expansion profile on
an A-copy is determined by a single top A-colour, even though the
expansion language has symbols of unbounded arity. The proof treats
ALL smaller labelled source embeddings, not only increasing subsets.

This module does NOT assume countable diary unavoidability or a
big Ramsey structure theorem. Numerically sharpness and each-colour
unavoidability are separate abstract hypotheses used by the next
assembly module.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open _root_.ThreeUniformDiaries.Ordered3Graph

/-- A coherent family of canonical colours on GENUINE finite induced
labelled embeddings into U. Surjectivity is part of the interface;
it is not inferred merely from the numerical degree. -/
structure CoherentFiniteColourSystem (U : Ordered3Graph Nat) where
  Palette : (n : Nat) → EnumNode n → Type
  finitePalette : ∀ {n : Nat} (A : EnumNode n), Finite (Palette n A)
  colour : {n : Nat} → (A : EnumNode n) →
    GenuineFiniteEmbeddings A U → Palette n A
  surj : ∀ {n : Nat} (A : EnumNode n),
    Function.Surjective (colour A)
  coherent : ∀ {a b : Nat} (A : EnumNode a) (B : EnumNode b)
    (i : Fin b → Fin a)
    (hi : IsInducedLabelledCopy B A.toOrdered3Graph
      (fun j => (i j).val))
    (v w : GenuineFiniteEmbeddings A U),
      colour A v = colour A w →
        colour B (v.precompose i hi) =
          colour B (w.precompose i hi)
  unavoidable : ∀ {n : Nat} (A : EnumNode n)
    (w : UnorderedEmbedding U U) (d : Palette n A),
      ∃ v : GenuineFiniteEmbeddings A U,
        colour A (v.postcompose w) = d

namespace CoherentFiniteColourSystem

variable {U : Ordered3Graph Nat} (C : CoherentFiniteColourSystem U)

/-- The additional RELATIONAL symbols of the expansion: source
arity, full enumerated source graph, and its corresponding colour.
The old unordered 3-edge relation is retained as the reduct. -/
structure RelationSymbol where
  arity : Nat
  source : EnumNode arity
  colour : C.Palette arity source

/-- Interpretation of a new relation symbol on a tuple of U.
Noncopies and tuples with repeated entries automatically fail. -/
def Relation (σ : RelationSymbol C) (v : Fin σ.arity → Nat) : Prop :=
  ∃ h : IsInducedLabelledCopy σ.source U v,
    C.colour σ.source ⟨v,h⟩ = σ.colour

/-- All new finite relations induced on an actual labelled A-copy.
These truth values are the complete induced EXPANSION profile.
We use the dependent tuple length of each relation symbol. -/
abbrev Profile {a : Nat} (_A : EnumNode a) : Type :=
  (σ : RelationSymbol C) → (Fin σ.arity → Fin a) → Prop

def inducedProfile {a : Nat} (A : EnumNode a)
    (v : GenuineFiniteEmbeddings A U) : Profile C A :=
  fun σ i => C.Relation σ (fun j => v.val (i j))

/-- Pulling back a selected B-copy through an induced A-copy
reflects inducedness in BOTH directions, even if labels are
permuted and the selected indices are not increasing. -/
theorem labelledSubcopy_iff_in_source
    {a b : Nat} (A : EnumNode a) (B : EnumNode b)
    (v : GenuineFiniteEmbeddings A U)
    (i : Fin b → Fin a) :
    IsInducedLabelledCopy B U (fun j => v.val (i j)) ↔
      IsInducedLabelledCopy B A.toOrdered3Graph
        (fun j => (i j).val) := by
  have hvFull :
      IsFiniteLabelledCopy A.toOrdered3Graph U a v.val :=
    (isInducedLabelledCopy_iff_fullUnordered A U v.val).mp v.property
  constructor
  · intro hB
    refine ⟨?_, ?_⟩
    · intro j k hjk
      apply hB.1
      have hFin : i j = i k := Fin.ext hjk
      exact congrArg v.val hFin
    · intro j k l hjk hkl
      exact (hB.2 j k l hjk hkl).trans
        (hvFull.2 (i j) (i k) (i l)).symm
  · intro hI
    exact isInducedLabelledCopy_precompose A B U i hI
      v.val v.property

/-- Evaluating an induced expansion relation at a true finite
source subembedding is EXACTLY evaluating its colour. -/
theorem inducedRelation_iff_subcopy_colour
    {a : Nat} (A : EnumNode a)
    (σ : RelationSymbol C)
    (i : Fin σ.arity → Fin a)
    (hi : IsInducedLabelledCopy σ.source A.toOrdered3Graph
      (fun j => (i j).val))
    (v : GenuineFiniteEmbeddings A U) :
    C.inducedProfile A v σ i ↔
      C.colour σ.source (v.precompose i hi) = σ.colour := by
  change (∃ h : IsInducedLabelledCopy σ.source U
    (fun j => v.val (i j)),
    C.colour σ.source ⟨(fun j => v.val (i j)),h⟩ = σ.colour) ↔ _
  constructor
  · rintro ⟨h, hc⟩
    exact hc
  · intro hc
    exact ⟨isInducedLabelledCopy_precompose
      A σ.source U i hi v.val v.property, hc⟩

/-- For any actual A-copy, the top-arity relation R_(A,d)
recognizes exactly its canonical A-colour. -/
theorem topRelation_iff_colour
    {a : Nat} (A : EnumNode a)
    (v : GenuineFiniteEmbeddings A U)
    (d : C.Palette a A) :
    C.inducedProfile A v ⟨a,A,d⟩ (fun j => j) ↔
      C.colour A v = d := by
  let hi : IsInducedLabelledCopy A A.toOrdered3Graph
      (fun j : Fin a => j.val) := finiteLabelledEmbedding_id A
  have h := C.inducedRelation_iff_subcopy_colour A
    ⟨a,A,d⟩ (fun j => j) hi v
  simpa only [GenuineFiniteEmbeddings.precompose_id] using h

/-- Coherence entails that the ENTIRE induced expansion on A,
including relations of every smaller source arity, depends
only on the TOP canonical A-colour. -/
theorem inducedProfile_eq_of_colour_eq
    {a : Nat} (A : EnumNode a)
    (v w : GenuineFiniteEmbeddings A U)
    (hSame : C.colour A v = C.colour A w) :
    C.inducedProfile A v = C.inducedProfile A w := by
  classical
  funext σ i
  apply propext
  by_cases hi : IsInducedLabelledCopy σ.source A.toOrdered3Graph
      (fun j => (i j).val)
  · rw [C.inducedRelation_iff_subcopy_colour A σ i hi v,
        C.inducedRelation_iff_subcopy_colour A σ i hi w]
    rw [C.coherent A σ.source i hi v w hSame]
  · constructor
    · intro h
      have hB : IsInducedLabelledCopy σ.source U
          (fun j => v.val (i j)) := h.1
      exact False.elim
        (hi ((labelledSubcopy_iff_in_source A σ.source v i).mp hB))
    · intro h
      have hB : IsInducedLabelledCopy σ.source U
          (fun j => w.val (i j)) := h.1
      exact False.elim
        (hi ((labelledSubcopy_iff_in_source A σ.source w i).mp hB))

/-- A full finite induced expansion profile can distinguish two
actual A-copies if and only if their top A-colours differ.
In particular NO extra expansion types are introduced by the
relations indexed by smaller arities. -/
theorem inducedProfile_eq_iff_colour_eq
    {a : Nat} (A : EnumNode a)
    (v w : GenuineFiniteEmbeddings A U) :
    C.inducedProfile A v = C.inducedProfile A w ↔
      C.colour A v = C.colour A w := by
  constructor
  · intro hp
    have hv : C.inducedProfile A v
        ⟨a,A,C.colour A v⟩ (fun j => j) :=
      (C.topRelation_iff_colour A v _).mpr rfl
    rw [hp] at hv
    exact ((C.topRelation_iff_colour A w _).mp hv).symm
  · exact C.inducedProfile_eq_of_colour_eq A v w

end CoherentFiniteColourSystem
end ATRFiniteDecoder
end ThreeUniformDiaries
