import ThreeUniformDiaries.DiaryCanonicalMarkedSubcopy
import ThreeUniformDiaries.DiaryCanonicalMarkedColourSurjective

/-!
# Canonical marked-diary COLOUR naturality on actual finite copies

The verified canonical-source restriction identity is promoted
to the actual total colourings of induced labelled copies of
A in U, after choosing a full RoleDiary leaf model U -> K.

For any induced labelled subembedding i:B -> A, raw restriction
of the full A-colour is LITERALLY the smaller B-colour.
Consequently the B-colour is constant on the fibres of the
A-colour; since every A-colour is unavoidable, it is surjective
and therefore induces a UNIQUE restriction map of finite
colour palettes. This proves exactly the mathematical
naturality equation needed by the big Ramsey structure.

No recurrence, countable diary unavoidability, or strong
diary-selfembedding is assumed.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open _root_.ThreeUniformDiaries.Ordered3Graph
open DiaryLeafPriority

/-- The actual canonical marked B-colour of a subcopy is the
raw finite marked-diary restriction of the canonical A-colour,
including arbitrary permutations of source labels. -/
theorem canonicalMarkedDiaryColour_restrict_raw
    {U K : Ordered3Graph Nat} (DK : RoleDiary K)
    (F : UnorderedEmbedding U K)
    (hFLeaf : ∀ x : Nat, IsLeaf K (F x))
    {a b : Nat} (A : EnumNode a) (B : EnumNode b)
    (i : Fin b → Fin a)
    (hi : IsInducedLabelledCopy B A.toOrdered3Graph
      (fun j => (i j).val))
    (v : GenuineFiniteEmbeddings A U) :
    ((canonicalMarkedDiaryColour DK F hFLeaf A v).val.rawRestrict i) =
      (canonicalMarkedDiaryColour DK F hFLeaf B
        (v.precompose i hi)).val := by
  classical
  let w : Fin a → Nat := fun j => F (v.val j)
  let wB : Fin b → Nat := fun j => w (i j)
  have hLeaf : ∀ j : Fin a, IsLeaf K (w j) :=
    fun j => hFLeaf (v.val j)
  have hA : IsInducedLabelledCopy A K w :=
    isInducedLabelledCopy_map_unordered A F v.val v.property
  have hB : IsInducedLabelledCopy B K wB := by
    exact isInducedLabelledCopy_map_unordered B F
      (fun j => v.val (i j))
      (isInducedLabelledCopy_precompose A B U i hi v.val v.property)
  change (canonicalMarkedSourceOfLeaves DK A w hLeaf hA).rawRestrict i =
    canonicalMarkedSourceOfLeaves DK B wB
      (fun j => hLeaf (i j)) hB
  exact canonicalMarkedSourceOfLeaves_rawRestrict
    DK A B w hLeaf hA i hB

/-- For each actual labelled inclusion i:B -> A, the
canonical B-colour is constant on the fibres of the
canonical A-colour. Unlike a mere cardinal calculation,
this is the crucial COHERENCE property of the colouring. -/
theorem canonicalMarkedDiaryColour_restrict_fibre
    {U K : Ordered3Graph Nat} (DK : RoleDiary K)
    (F : UnorderedEmbedding U K)
    (hFLeaf : ∀ x : Nat, IsLeaf K (F x))
    {a b : Nat} (A : EnumNode a) (B : EnumNode b)
    (i : Fin b → Fin a)
    (hi : IsInducedLabelledCopy B A.toOrdered3Graph
      (fun j => (i j).val)) :
    ∀ x y : GenuineFiniteEmbeddings A U,
      canonicalMarkedDiaryColour DK F hFLeaf A x =
        canonicalMarkedDiaryColour DK F hFLeaf A y →
      canonicalMarkedDiaryColour DK F hFLeaf B
          (x.precompose i hi) =
        canonicalMarkedDiaryColour DK F hFLeaf B
          (y.precompose i hi) := by
  intro x y hxy
  apply Subtype.ext
  have hx := canonicalMarkedDiaryColour_restrict_raw
    DK F hFLeaf A B i hi x
  have hy := canonicalMarkedDiaryColour_restrict_raw
    DK F hFLeaf A B i hi y
  calc
    (canonicalMarkedDiaryColour DK F hFLeaf B
        (x.precompose i hi)).val =
        (canonicalMarkedDiaryColour DK F hFLeaf A x).val.rawRestrict i :=
      hx.symm
    _ = (canonicalMarkedDiaryColour DK F hFLeaf A y).val.rawRestrict i :=
      congrArg (fun P : MarkedFiniteSource 0 a => P.rawRestrict i)
        (congrArg Subtype.val hxy)
    _ = (canonicalMarkedDiaryColour DK F hFLeaf B
        (y.precompose i hi)).val := hy

/-- The actual full marked A-colour induces a UNIQUE palette
restriction map rho_i. Surjectivity is derived from genuine
finite-source every-colour unavoidability, not assumed. -/
theorem canonicalMarkedDiaryColour_restriction_existsUnique
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
    ∃! ρ : GenuineMarkedDiaryTypes A → GenuineMarkedDiaryTypes B,
      ∀ v : GenuineFiniteEmbeddings A U,
        ρ (canonicalMarkedDiaryColour DK F hFLeaf A v) =
          canonicalMarkedDiaryColour DK F hFLeaf B
            (v.precompose i hi) := by
  have hSurj : Function.Surjective
      (canonicalMarkedDiaryColour DK F hFLeaf A) :=
    canonicalMarkedDiaryColour_surjective
      G U K hUniversal DK F hFLeaf A
  exact (colourRestriction_existsUnique_iff_fibre
    (canonicalMarkedDiaryColour DK F hFLeaf A)
    (fun v : GenuineFiniteEmbeddings A U =>
      canonicalMarkedDiaryColour DK F hFLeaf B (v.precompose i hi))
    hSurj).mpr
      (canonicalMarkedDiaryColour_restrict_fibre
        DK F hFLeaf A B i hi)

end ATRFiniteDecoder
end ThreeUniformDiaries
