import ThreeUniformDiaries.DiaryCanonicalMarkedColourNaturality
import ThreeUniformDiaries.DiaryCanonicalMarkedSubcopyComposition

/-!
# Canonical marked-diary palette restriction is a contravariant functor

For every finite induced labelled embedding i:B -> A (including
arbitrary label permutations), the complete marked A-diary colour
has a UNIQUE induced B-colour. Every A-colour occurs in the
fixed full diary leaf model, so a restriction map is defined on
the entire genuine finite palette, not just on colours of a
particular embedding.

The identity and composition laws follow by evaluating the
maps on an actual A-copy and using colour surjectivity. No
unverified compactness or countable diary Ramsey property is
needed.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open _root_.ThreeUniformDiaries.Ordered3Graph
open DiaryLeafPriority

/-- The unique actual restriction of complete marked diary
colours along a finite induced embedding B -> A. -/
noncomputable def canonicalMarkedDiaryRestriction
    (G : GenericEnumerated3Graph)
    (U K : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    (DK : RoleDiary K)
    (F : UnorderedEmbedding U K)
    (hFLeaf : ∀ x : Nat, IsLeaf K (F x))
    {a b : Nat} (A : EnumNode a) (B : EnumNode b)
    (i : Fin b → Fin a)
    (hi : IsInducedLabelledCopy B A.toOrdered3Graph
      (fun j => (i j).val)) :
    GenuineMarkedDiaryTypes A → GenuineMarkedDiaryTypes B :=
  Classical.choose
    (canonicalMarkedDiaryColour_restriction_existsUnique
      G U K hUniversal DK F hFLeaf A B i hi)

/-- Naturality equation on every actual induced labelled A-copy. -/
theorem canonicalMarkedDiaryRestriction_spec
    (G : GenericEnumerated3Graph)
    (U K : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    (DK : RoleDiary K)
    (F : UnorderedEmbedding U K)
    (hFLeaf : ∀ x : Nat, IsLeaf K (F x))
    {a b : Nat} (A : EnumNode a) (B : EnumNode b)
    (i : Fin b → Fin a)
    (hi : IsInducedLabelledCopy B A.toOrdered3Graph
      (fun j => (i j).val))
    (v : GenuineFiniteEmbeddings A U) :
    canonicalMarkedDiaryRestriction
        G U K hUniversal DK F hFLeaf A B i hi
        (canonicalMarkedDiaryColour DK F hFLeaf A v) =
      canonicalMarkedDiaryColour DK F hFLeaf B
        (v.precompose i hi) := by
  exact (Classical.choose_spec
    (canonicalMarkedDiaryColour_restriction_existsUnique
      G U K hUniversal DK F hFLeaf A B i hi)).1 v

/-- The palette restriction along the identity finite labelled
embedding is literally the identity on all genuine marked colours. -/
theorem canonicalMarkedDiaryRestriction_id
    (G : GenericEnumerated3Graph)
    (U K : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    (DK : RoleDiary K)
    (F : UnorderedEmbedding U K)
    (hFLeaf : ∀ x : Nat, IsLeaf K (F x))
    {a : Nat} (A : EnumNode a) :
    canonicalMarkedDiaryRestriction
        G U K hUniversal DK F hFLeaf A A (fun j => j)
        (finiteLabelledEmbedding_id A) = id := by
  funext d
  obtain ⟨v,hv⟩ :=
    (canonicalMarkedDiaryColour_surjective
      G U K hUniversal DK F hFLeaf A) d
  have hSpec := canonicalMarkedDiaryRestriction_spec
    G U K hUniversal DK F hFLeaf A A
    (fun j => j) (finiteLabelledEmbedding_id A) v
  have hId := GenuineFiniteEmbeddings.precompose_id v
  rw [hId] at hSpec
  rw [← hv]
  exact hSpec

/-- Palette restriction is contravariantly functorial:
restricting from A to B and then to C equals restricting
directly from A to C, with any source label permutations. -/
theorem canonicalMarkedDiaryRestriction_comp
    (G : GenericEnumerated3Graph)
    (U K : Ordered3Graph Nat)
    (hUniversal : CountablyUniversal U)
    (DK : RoleDiary K)
    (F : UnorderedEmbedding U K)
    (hFLeaf : ∀ x : Nat, IsLeaf K (F x))
    {a b c : Nat} (A : EnumNode a) (B : EnumNode b) (C : EnumNode c)
    (i : Fin b → Fin a) (j : Fin c → Fin b)
    (hi : IsInducedLabelledCopy B A.toOrdered3Graph
      (fun t => (i t).val))
    (hj : IsInducedLabelledCopy C B.toOrdered3Graph
      (fun t => (j t).val)) :
    canonicalMarkedDiaryRestriction
        G U K hUniversal DK F hFLeaf A C (fun t => i (j t))
        (finiteLabelledEmbedding_comp A B C i j hi hj) =
      (canonicalMarkedDiaryRestriction
        G U K hUniversal DK F hFLeaf B C j hj) ∘
      (canonicalMarkedDiaryRestriction
        G U K hUniversal DK F hFLeaf A B i hi) := by
  funext d
  obtain ⟨v,hv⟩ :=
    (canonicalMarkedDiaryColour_surjective
      G U K hUniversal DK F hFLeaf A) d
  let ρi := canonicalMarkedDiaryRestriction
    G U K hUniversal DK F hFLeaf A B i hi
  let ρj := canonicalMarkedDiaryRestriction
    G U K hUniversal DK F hFLeaf B C j hj
  let ρcomp := canonicalMarkedDiaryRestriction
    G U K hUniversal DK F hFLeaf A C (fun t => i (j t))
    (finiteLabelledEmbedding_comp A B C i j hi hj)
  have hComp := canonicalMarkedDiaryRestriction_spec
    G U K hUniversal DK F hFLeaf A C (fun t => i (j t))
    (finiteLabelledEmbedding_comp A B C i j hi hj) v
  have hI := canonicalMarkedDiaryRestriction_spec
    G U K hUniversal DK F hFLeaf A B i hi v
  have hJ := canonicalMarkedDiaryRestriction_spec
    G U K hUniversal DK F hFLeaf B C j hj
    (v.precompose i hi)
  have hPrecomp := GenuineFiniteEmbeddings.precompose_comp
    v i j hi hj
  change ρcomp d = (ρj ∘ ρi) d
  rw [← hv]
  change ρcomp (canonicalMarkedDiaryColour DK F hFLeaf A v) =
    ρj (ρi (canonicalMarkedDiaryColour DK F hFLeaf A v))
  calc
    ρcomp (canonicalMarkedDiaryColour DK F hFLeaf A v) =
      canonicalMarkedDiaryColour DK F hFLeaf C
        (v.precompose (fun t => i (j t))
          (finiteLabelledEmbedding_comp A B C i j hi hj)) := hComp
    _ = canonicalMarkedDiaryColour DK F hFLeaf C
        ((v.precompose i hi).precompose j hj) := by
          rw [hPrecomp]
    _ = ρj (canonicalMarkedDiaryColour DK F hFLeaf B
        (v.precompose i hi)) := hJ.symm
    _ = ρj (ρi (canonicalMarkedDiaryColour DK F hFLeaf A v)) := by
          rw [← hI]

end ATRFiniteDecoder
end ThreeUniformDiaries
