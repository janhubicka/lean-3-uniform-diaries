import ThreeUniformDiaries.DiaryFiniteATRShapeUniverse
import ThreeUniformDiaries.DiaryFiniteSingletonColour
import ThreeUniformDiaries.DiaryFinitePairColour

/-!
# One finite ATR stage stabilising all small-envelope type colours

At a fixed protected source cut n and target cut N, the complete
colour of a finite envelope records:
* the target singleton 1-type of its penultimate vertex;
* the target singleton 1-type of its last vertex;
* the target auxiliary 2-type and lexicographic orientation of that
  ordered pair.

Singleton envelopes have just one exterior vertex, so their
penultimate index (if present) may lie inside the protected prefix.
For pointed envelopes with two or three exterior vertices, the
last two source indices are exactly the distinguished leaf pair.
No claim is made that F preserves the order of those images.

There are FINITELY many small native EnumNode sources at n, thanks
to the finite-source universe. The checked simultaneous finite ATR
theorem therefore homogenises the complete colour of EVERY such
source by one prefix-fixing aux-type-respecting refinement.

This eliminates the need to stabilise singleton and pair source
shapes in two separate finite iteration loops, without changing
any of the lower-bound hypotheses. Finite forbidden-set avoidance,
recursive stage construction and countable fusion remain separate.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- A single finite product colour encoding two target singleton
types and one target auxiliary-pair type plus orientation. -/
abbrev FullEnvelopeColour (N : Nat) : Type :=
  ((Fin N → Fin N → Bool) × (Fin N → Fin N → Bool)) ×
    ((Fin N → Bool) × Bool)

/-- Last actual vertex of an arbitrary protected finite source. -/
def ProtectedSource.lastIndex {n : Nat}
    (A : ProtectedSource n) : Fin (A.k+1) :=
  Fin.last A.k

/-- Penultimate actual vertex, when it exists. For a one-vertex
source we reuse the last index, yielding a total colour function. -/
def ProtectedSource.penultimateIndex {n : Nat}
    (A : ProtectedSource n) : Fin (A.k+1) :=
  if hk : 0 < A.k then
    ⟨A.k-1, by omega⟩
  else A.lastIndex

/-- The target cut N and arbitrary outer map F determine a genuinely
finite colouring of the actual images of each finite source. -/
noncomputable def fullEnvelopeColour
    (K : Ordered3Graph Nat) (F : Nat → Nat) (N : Nat)
    {G : GenericEnumerated3Graph} {n : Nat}
    (A : ProtectedSource n) (e : A.Code G) :
    FullEnvelopeColour N :=
  let x := F (e.image A.penultimateIndex)
  let y := F (e.image A.lastIndex)
  ((DiaryLowerBoundColors.singletonColour K N x,
    DiaryLowerBoundColors.singletonColour K N y),
    DiaryLowerBoundColors.pairColour K N x y)

/-- Equality of complete finite colours is EXACTLY simultaneous
agreement of the two 1-types, the auxiliary 2-type, and the
lexicographic orientation in the arbitrary target graph. -/
theorem fullEnvelopeColour_eq_iff
    (K : Ordered3Graph Nat) (F : Nat → Nat) (N : Nat)
    {G : GenericEnumerated3Graph} {n : Nat}
    (A : ProtectedSource n) (e₀ e₁ : A.Code G) :
    fullEnvelopeColour K F N A e₀ =
        fullEnvelopeColour K F N A e₁ ↔
      K.SameOneTypeBelow N
        (F (e₀.image A.penultimateIndex))
        (F (e₁.image A.penultimateIndex)) ∧
      K.SameOneTypeBelow N
        (F (e₀.image A.lastIndex))
        (F (e₁.image A.lastIndex)) ∧
      K.SameAuxTypeBelow N
        (F (e₀.image A.penultimateIndex))
        (F (e₀.image A.lastIndex))
        (F (e₁.image A.penultimateIndex))
        (F (e₁.image A.lastIndex)) ∧
      (DiaryLeafPriority.LexEarlier K
          (F (e₀.image A.penultimateIndex))
          (F (e₀.image A.lastIndex)) ↔
       DiaryLeafPriority.LexEarlier K
          (F (e₁.image A.penultimateIndex))
          (F (e₁.image A.lastIndex))) := by
  classical
  let x₀ := F (e₀.image A.penultimateIndex)
  let y₀ := F (e₀.image A.lastIndex)
  let x₁ := F (e₁.image A.penultimateIndex)
  let y₁ := F (e₁.image A.lastIndex)
  change
    ((DiaryLowerBoundColors.singletonColour K N x₀,
      DiaryLowerBoundColors.singletonColour K N y₀),
      DiaryLowerBoundColors.pairColour K N x₀ y₀) =
    ((DiaryLowerBoundColors.singletonColour K N x₁,
      DiaryLowerBoundColors.singletonColour K N y₁),
      DiaryLowerBoundColors.pairColour K N x₁ y₁) ↔
      K.SameOneTypeBelow N x₀ x₁ ∧
      K.SameOneTypeBelow N y₀ y₁ ∧
      K.SameAuxTypeBelow N x₀ y₀ x₁ y₁ ∧
      (DiaryLeafPriority.LexEarlier K x₀ y₀ ↔
        DiaryLeafPriority.LexEarlier K x₁ y₁)
  constructor
  · intro h
    have hleft := congrArg Prod.fst h
    have hright := congrArg Prod.snd h
    have hx := congrArg Prod.fst hleft
    have hy := congrArg Prod.snd hleft
    have hxy :=
      (DiaryLowerBoundColors.pairColour_eq_iff
        K N x₀ y₀ x₁ y₁).mp hright
    exact ⟨(DiaryLowerBoundColors.singletonColour_eq_iff
        K N x₀ x₁).mp hx,
      (DiaryLowerBoundColors.singletonColour_eq_iff
        K N y₀ y₁).mp hy, hxy.1, hxy.2⟩
  · rintro ⟨hx, hy, haux, hlex⟩
    apply Prod.ext
    · apply Prod.ext
      · exact (DiaryLowerBoundColors.singletonColour_eq_iff
          K N x₀ x₁).mpr hx
      · exact (DiaryLowerBoundColors.singletonColour_eq_iff
          K N y₀ y₁).mpr hy
    · exact (DiaryLowerBoundColors.pairColour_eq_iff
        K N x₀ y₀ x₁ y₁).mpr ⟨haux, hlex⟩

/-- A single protected-prefix refinement homogenises every complete
1-type, auxiliary 2-type, and orientation colour on every possible
one-, two-, or three-tail finite ATR source simultaneously. No
finite list of actual pair witnesses or extra marker axioms is
required; incompatible finite sources contribute vacuous clauses. -/
theorem actualFiniteAuxRamsey_allSmallEnvelopeColours
    (G : GenericEnumerated3Graph) (n : Nat)
    (K : Ordered3Graph Nat) (F : Nat → Nat) (N : Nat) :
    ∃ (u : Embedding G.graph G.graph)
      (hu : u.AuxTypeRespecting),
      (∀ t < n, u t = t) ∧
      ∀ A ∈ smallSourceUniverse n,
        ∃ color : FullEnvelopeColour N,
          ∀ e : A.Code G, A.FixesPrefix G e →
            fullEnvelopeColour K F N A
              (e.postcompose u hu) = color := by
  let χ : ∀ A : ProtectedSource n, A.Code G → FullEnvelopeColour N :=
    fun A e => fullEnvelopeColour K F N A e
  exact actualFiniteAuxRamsey_smallSourceUniverse G n χ

end ATRFiniteDecoder
end ThreeUniformDiaries
