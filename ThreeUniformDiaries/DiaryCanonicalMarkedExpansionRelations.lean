import ThreeUniformDiaries.DiaryCanonicalMarkedColourSurjective

/-!
# The actual canonical marked-diary expansion relations

The proposed big Ramsey expansion has one relation symbol for each
finite enumerated hypergraph A and each genuine marked A-diary d.
This file defines its actual interpretation on labelled finite tuples.

The relations:
* are false on tuples that are not genuine induced A-embeddings;
* partition the genuine A-embeddings into exactly one d-colour;
* realize every d inside EVERY unordered induced U-selfcopy.

These unconditional properties follow from the existing finite-source
canonical colouring and its independent unavoidability theorem.

This is NOT yet a Big Ramsey Structure theorem: to obtain that, one
still must prove NATURALITY of marked codes under arbitrary finite
subembedding B -> A, so that the full induced expansion on A depends
only on its top marked A-colour.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open _root_.ThreeUniformDiaries.Ordered3Graph
open DiaryLeafPriority

/-- A concrete relational interpretation, parameterized by the
canonical marked A-source d, on a labelled tuple in U.
The source tuple need not be numerically increasing. -/
noncomputable def canonicalMarkedExpansionRelation
    {U K : Ordered3Graph Nat}
    (DK : RoleDiary K)
    (F : UnorderedEmbedding U K)
    (hFLeaf : ∀ x : Nat, IsLeaf K (F x))
    {a : Nat} (A : EnumNode a)
    (d : GenuineMarkedDiaryTypes A)
    (v : Fin a → Nat) : Prop :=
  ∃ hv : IsInducedLabelledCopy A U v,
    canonicalMarkedDiaryColour DK F hFLeaf A ⟨v, hv⟩ = d

/-- On a genuine A-copy, membership in the d-relation says
EXACTLY that the canonical marked-diary colour is d. -/
theorem canonicalMarkedExpansionRelation_iff
    {U K : Ordered3Graph Nat}
    (DK : RoleDiary K)
    (F : UnorderedEmbedding U K)
    (hFLeaf : ∀ x : Nat, IsLeaf K (F x))
    {a : Nat} (A : EnumNode a)
    (d : GenuineMarkedDiaryTypes A)
    (v : Fin a → Nat)
    (hv : IsInducedLabelledCopy A U v) :
    canonicalMarkedExpansionRelation DK F hFLeaf A d v ↔
      canonicalMarkedDiaryColour DK F hFLeaf A ⟨v, hv⟩ = d := by
  constructor
  · rintro ⟨hv', heq⟩
    simpa only using heq
  · intro heq
    exact ⟨hv, heq⟩

/-- The expansion's d-relations partition EVERY genuine
labelled A-copy into exactly one canonical marked A-colour.
This does not rely on the missing cross-arity naturality. -/
theorem canonicalMarkedExpansionRelation_existsUnique
    {U K : Ordered3Graph Nat}
    (DK : RoleDiary K)
    (F : UnorderedEmbedding U K)
    (hFLeaf : ∀ x : Nat, IsLeaf K (F x))
    {a : Nat} (A : EnumNode a)
    (v : Fin a → Nat)
    (hv : IsInducedLabelledCopy A U v) :
    ∃! d : GenuineMarkedDiaryTypes A,
      canonicalMarkedExpansionRelation DK F hFLeaf A d v := by
  let d : GenuineMarkedDiaryTypes A :=
    canonicalMarkedDiaryColour DK F hFLeaf A ⟨v, hv⟩
  refine ⟨d, ⟨hv, rfl⟩, ?_⟩
  intro e he
  exact ((canonicalMarkedExpansionRelation_iff
      DK F hFLeaf A e v hv).mp he).symm

/-- The canonical expansion relations do not spuriously hold
on a tuple that fails to be an induced A-embedding. -/
theorem canonicalMarkedExpansionRelation_false_of_not_copy
    {U K : Ordered3Graph Nat}
    (DK : RoleDiary K)
    (F : UnorderedEmbedding U K)
    (hFLeaf : ∀ x : Nat, IsLeaf K (F x))
    {a : Nat} (A : EnumNode a)
    (d : GenuineMarkedDiaryTypes A)
    (v : Fin a → Nat)
    (hv : ¬ IsInducedLabelledCopy A U v) :
    ¬ canonicalMarkedExpansionRelation DK F hFLeaf A d v := by
  rintro ⟨hCopy, _⟩
  exact hv hCopy

/-- EVERY genuine marked expansion relation occurs inside
EVERY unordered induced selfcopy of U. This is a concrete,
UNCONDITIONAL consequence of finite-source marked diary
unavoidability, not of the unproved countable-source theorem. -/
theorem canonicalMarkedExpansionRelation_unavoidable
    (G : GenericEnumerated3Graph)
    (U K : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    (DK : RoleDiary K)
    (F : UnorderedEmbedding U K)
    (hFLeaf : ∀ x : Nat, IsLeaf K (F x))
    {a : Nat} (A : EnumNode a)
    (w : UnorderedEmbedding U U)
    (d : GenuineMarkedDiaryTypes A) :
    ∃ v : GenuineFiniteEmbeddings A U,
      canonicalMarkedExpansionRelation DK F hFLeaf A d
        (fun i : Fin a => w (v.val i)) := by
  obtain ⟨v, hv⟩ :=
    (canonicalMarkedDiaryColour_unavoidable
      G U K hUniversal DK F hFLeaf A) w d
  refine ⟨v, ?_⟩
  have hCopy : IsInducedLabelledCopy A U
      (fun i : Fin a => w (v.val i)) :=
    isInducedLabelledCopy_map_unordered A w v.val v.property
  refine ⟨hCopy, ?_⟩
  simpa only [GenuineFiniteEmbeddings.postcompose] using hv

end ATRFiniteDecoder
end ThreeUniformDiaries
