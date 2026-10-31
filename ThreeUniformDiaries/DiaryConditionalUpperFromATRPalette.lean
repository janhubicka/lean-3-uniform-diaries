import ThreeUniformDiaries.ActualFiniteAuxPalette

/-!
# Track C: non-circular conditional upper bound from genuine ATR codes

The current manuscript's upper-bound argument conflates:
* a finite family of genuinely auxiliary-type-respecting source codes;
* an arbitrary finite A-copy inside the selected diary leaf reduct.

The first family already has a verified finite Ramsey palette.
The substantive missing theorem is a *cover*: every selected copy
must be represented by one of those genuine finite ATR codes.

This file turns that cover into an EXPLICIT hypothesis and derives
the precise finite-colour conclusion.  The hypothesis must hold
for the self-embedding chosen by the finite ATR palette theorem:
the selected range may depend on that self-embedding.

There is no use of the full diary Ramsey theorem, countable diary
unavoidability, an automorphism count, or an unchecked implication
from type-respectingness to auxiliary-type-respectingness.

This is a correct conditional theorem, NOT a proof of the complete
upper bound. To instantiate it for diaries one must independently
construct the selected range (using countable unavoidability) and
the genuine auxiliary source-code factorisation (currently open).
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- For a finite list of genuine auxiliary finite source shapes,
suppose each possible selected copy admits one of their actual
ATR-code representations AFTER the common refinement.

Then the selected copies use at most one colour per source shape.

The `selected` set may vary with the chosen refinement; in the
intended application it consists of A-copies inside a diary
self-copy placed in the refined generic range.  The stronger,
unverified geometric fact is made explicit in `hCover`. -/
theorem actualFiniteAuxRamsey_palette_of_covered_codes
    (G : GenericEnumerated3Graph)
    (family : List (ProtectedSource 0))
    {X κ : Type}
    [Fintype κ] [Nonempty κ]
    (realize : ∀ A : ProtectedSource 0, A.Code G → X)
    (χ : X → κ)
    (selected :
      ∀ (u : Embedding G.graph G.graph),
        u.AuxTypeRespecting → X → Prop)
    (hCover :
      ∀ (u : Embedding G.graph G.graph)
        (hu : u.AuxTypeRespecting) (x : X),
        selected u hu x →
        ∃ A : ProtectedSource 0, A ∈ family ∧
          ∃ e : A.Code G, x = realize A (e.postcompose u hu)) :
    ∃ (u : Embedding G.graph G.graph)
      (hu : u.AuxTypeRespecting),
      ∃ palette : List κ,
        palette.length = family.length ∧
        ∀ x : X, selected u hu x → χ x ∈ palette := by
  let colors : ∀ A : ProtectedSource 0, A.Code G → κ :=
    fun A e => χ (realize A e)
  obtain ⟨u, hu, palette, hlen, hpalette⟩ :=
    actualFiniteAuxRamsey_zeroCut_palette G colors family
  refine ⟨u, hu, palette, hlen, ?_⟩
  intro x hx
  obtain ⟨A, hA, e, heq⟩ := hCover u hu x hx
  rw [heq]
  exact hpalette A hA e

end ATRFiniteDecoder
end ThreeUniformDiaries
