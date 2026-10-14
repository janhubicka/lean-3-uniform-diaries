import ThreeUniformDiaries.ActualFiniteAuxRamseyAll
import ThreeUniformDiaries.FiniteAuxEmbeddingPostcomposition

/-!
# Simultaneous finite ATR stabilisation at a protected prefix

The lower-bound proof homogenises finitely many one-vertex and pointed
pair-envelope shapes, using the very same generic self-embedding at
the end. This is a purely formal finite iteration of the already
verified actual finite ATR theorem. It does NOT use a zero-extended
source tail as colouring data, and does not assume an infinite fusion
or any diary-specific orientation condition.

At each stage the new finite colouring is pulled back through the
previous self-embedding. The resulting self-embedding is composed
on the right with the new homogeneous refinement. Earlier colours
remain constant because postcomposition of genuine finite codes is
associative and the new refinement fixes the protected prefix.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- A genuine finite ATR source with enough real vertices to
contain the protected prefix. Source sizes are k+1, exactly as
in the unconditional finite theorem. -/
structure ProtectedSource (n : Nat) where
  k : Nat
  picture : EnumNode (k + 1)
  cut_le : n ≤ k + 1

/-- The extensional actual-finite-vertex embedding code of a
protected finite source into the enumerated generic hypergraph. -/
abbrev ProtectedSource.Code
    (G : GenericEnumerated3Graph) {n : Nat}
    (A : ProtectedSource n) : Type :=
  FiniteAuxEmbeddingImage A.picture.toOrdered3Graph G.graph (A.k + 1)

/-- The literal initial-prefix-fixing condition on a finite
embedding, independent of any chosen extension tail. -/
def ProtectedSource.FixesPrefix
    (G : GenericEnumerated3Graph) {n : Nat}
    (A : ProtectedSource n) (e : A.Code G) : Prop :=
  ∀ i : Fin (A.k + 1), i.val < n → e.image i = i.val

/-- A homogeneous finite colour stays homogeneous after every
further aux-type-respecting refinement fixing the same prefix.
This is the preservation invariant needed in the manuscript's
successive stage construction. -/
theorem protected_colour_persists
    (G : GenericEnumerated3Graph) (n : Nat)
    (A : ProtectedSource n)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : A.Code G → κ)
    (g h : Embedding G.graph G.graph)
    (hg : g.AuxTypeRespecting) (hh : h.AuxTypeRespecting)
    (hfix : ∀ t < n, h t = t)
    (color : κ)
    (hcolour : ∀ e : A.Code G, A.FixesPrefix G e →
      χ (e.postcompose g hg) = color) :
    ∀ e : A.Code G, A.FixesPrefix G e →
      χ (e.postcompose (g.comp h) (hg.comp hh)) = color := by
  intro e he
  have hfixNew : A.FixesPrefix G (e.postcompose h hh) := by
    intro i hi
    simp only [FiniteAuxEmbeddingImage.postcompose_apply, he i hi,
      hfix i.val hi]
  have h := hcolour (e.postcompose h hh) hfixNew
  simpa only [FiniteAuxEmbeddingImage.postcompose_comp] using h

/-- Simultaneous homogeneity for an arbitrary finite list of
possibly different actual finite ATR sources over the same cut.
Every source is coloured on its own finite-image code space.
The ONE output embedding fixes the protected prefix and
homogenises all listed sources. -/
theorem actualFiniteAuxRamsey_finiteFamily
    (G : GenericEnumerated3Graph) (n : Nat)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : ∀ A : ProtectedSource n, A.Code G → κ)
    (family : List (ProtectedSource n)) :
    ∃ (u : Embedding G.graph G.graph)
      (hu : u.AuxTypeRespecting),
      (∀ t < n, u t = t) ∧
      ∀ A ∈ family,
        ∃ color : κ, ∀ e : A.Code G,
          A.FixesPrefix G e →
          χ A (e.postcompose u hu) = color := by
  induction family with
  | nil =>
      let u : Embedding G.graph G.graph := {
        toFun := fun i => i
        strictMono := by intro i j hij; exact hij
        edge_iff := by intro i j k hij hjk; exact Iff.rfl
      }
      have hu : u.AuxTypeRespecting := by
        constructor
        · intro l a b hla hlb
          exact Iff.rfl
        · intro l a b c d hla hab hlc hcd
          exact Iff.rfl
      refine ⟨u, hu, ?_, ?_⟩
      · intro t ht
        rfl
      · intro A hmem
        exact False.elim (List.not_mem_nil hmem)
  | cons A rest ih =>
      obtain ⟨g, hg, hfixg, hrest⟩ := ih
      let ρ : A.Code G → κ :=
        fun e => χ A (e.postcompose g hg)
      obtain ⟨h, hh, hfixh, colorA, hcolA⟩ :=
        actualFiniteAuxRamsey_allFinite G
          (n := n) (k := A.k) A.cut_le A.picture ρ
      let u : Embedding G.graph G.graph := g.comp h
      have hu : u.AuxTypeRespecting := hg.comp hh
      have hfixu : ∀ t < n, u t = t := by
        intro t ht
        change g (h t) = t
        rw [hfixh t ht, hfixg t ht]
      refine ⟨u, hu, hfixu, ?_⟩
      intro B hmem
      rcases List.mem_cons.mp hmem with hBA | hBrest
      · subst B
        refine ⟨colorA, ?_⟩
        intro e he
        have hc : ρ (e.postcompose h hh) = colorA :=
          hcolA e he
        change χ A ((e.postcompose h hh).postcompose g hg) =
          colorA at hc
        simpa only [FiniteAuxEmbeddingImage.postcompose_comp] using hc
      · obtain ⟨colorB, hcolB⟩ := hrest B hBrest
        refine ⟨colorB, ?_⟩
        intro e he
        exact protected_colour_persists G n B (χ B)
          g h hg hh hfixh colorB hcolB e he

end ATRFiniteDecoder
end ThreeUniformDiaries
