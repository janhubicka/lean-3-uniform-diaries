import ThreeUniformDiaries.DiaryUpperBoundDirectTransfer
import ThreeUniformDiaries.DiaryUpperBoundFiniteMarkedUniverse

/-!
# Track B: direct upper-bound transfer needs no ordered outer embedding

The existing direct-transfer endpoint asks for an ORDERED induced
embedding phi : K -> G before the finite diary cover is tested. The
big-Ramsey upper bound for arbitrary universal K, however, concerns
its UNORDERED hypergraph reduct; the prescribed identification of
K with leaves of a diary need not respect K's original enumeration.

This module removes the unnecessary monotonicity assumption on
phi. A genuine UNORDERED induced embedding K -> G suffices for the
ambient self-copy; the missing bounded source-code factorisation
remains an explicit hypothesis, checked pointwise at phi(v_i).

The second theorem composes this with the already verified complete
FINITE list of all bounded marked ATR sources. This proves a finite
uniform colour bound whenever a uniform finite-support factorisation
is available. It does NOT establish the sharp diary count or the
unconditional factorisation; those remain separate geometric tasks.

No countable diary unavoidability or full diary Ramsey is used.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- The direct noncircular upper bound requires merely an induced
embedding of UNDERLYING UNORDERED hypergraphs K -> G. There is no
order requirement on the supplied initial map phi.

The exact finite marked auxiliary factorisation hypothesis is
independent and remains stated explicitly. -/
theorem actualFiniteAuxRamsey_direct_upper_unordered_of_factorisation
    (G : GenericEnumerated3Graph)
    (K : Ordered3Graph Nat)
    {a : Nat} (A : EnumNode a)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (phi : UnorderedEmbedding K G.graph)
    (psi : UnorderedEmbedding G.graph K)
    (χ : (Fin a → Nat) → κ)
    (family : List (MarkedFiniteSource 0 a))
    (hFactors :
      ∀ v : Fin a → Nat,
        IsInducedLabelledCopy A K v →
        ∃ S ∈ family, ∃ e : S.source.Code G,
          ∀ i : Fin a, phi (v i) = e.image (S.marked i)) :
    ∃ w : UnorderedEmbedding K K,
      ∃ palette : List κ,
        palette.length = family.length ∧
        ∀ v : Fin a → Nat,
          IsInducedLabelledCopy A K v →
          χ (fun i => w (v i)) ∈ palette := by
  obtain ⟨u, hu, palette, hlen, hpalette⟩ :=
    actualFiniteAuxRamsey_markedPalette_zero
      G a psi.toFun χ family
  let w : UnorderedEmbedding K K :=
    psi.comp ((u.asUnordered).comp phi)
  refine ⟨w, palette, hlen, ?_⟩
  intro v hv
  have hfactor :
      ∃ S ∈ family, ∃ e : S.source.Code G,
        ∀ i : Fin a, phi (v i) = e.image (S.marked i) :=
    hFactors v hv
  have hc := hpalette (fun i => phi (v i)) hfactor
  change χ (fun i => psi (u (phi (v i)))) ∈ palette
  exact hc

/-- A uniform bound M on the size of genuine finite marked ATR
sources is enough to obtain a finite palette from the canonical
complete BOUNDED marked-source universe.

The bound is intentionally coarse. No claim is made that the list
contains only realizable full diary shapes, or that its length
equals the sharp big Ramsey degree. -/
theorem actualFiniteAuxRamsey_direct_upper_unordered_of_bounded_factorisation
    (G : GenericEnumerated3Graph)
    (K : Ordered3Graph Nat)
    {a : Nat} (A : EnumNode a)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (phi : UnorderedEmbedding K G.graph)
    (psi : UnorderedEmbedding G.graph K)
    (χ : (Fin a → Nat) → κ)
    (M : Nat)
    (hBoundedFactors :
      ∀ v : Fin a → Nat,
        IsInducedLabelledCopy A K v →
        ∃ S : MarkedFiniteSource 0 a,
          S.source.k + 1 ≤ M ∧
          ∃ e : S.source.Code G,
            ∀ i : Fin a, phi (v i) = e.image (S.marked i)) :
    ∃ w : UnorderedEmbedding K K,
      ∃ palette : List κ,
        palette.length = (boundedMarkedATRUniverse a M).length ∧
        ∀ v : Fin a → Nat,
          IsInducedLabelledCopy A K v →
          χ (fun i => w (v i)) ∈ palette := by
  apply actualFiniteAuxRamsey_direct_upper_unordered_of_factorisation
    G K A phi psi χ (boundedMarkedATRUniverse a M)
  intro v hv
  obtain ⟨S, hsize, e, he⟩ := hBoundedFactors v hv
  exact ⟨S, markedSource_mem_boundedATRUniverse S hsize, e, he⟩

end ATRFiniteDecoder
end ThreeUniformDiaries
