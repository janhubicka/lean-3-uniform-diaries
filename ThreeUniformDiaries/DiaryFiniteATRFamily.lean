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

/-- An individually coloured occurrence of a finite source. Two tasks may
have the SAME finite source graph but DIFFERENT colour pullbacks, for
instance from distinct leaf identifications or diary enumerations. -/
structure FiniteATRColourTask
    (G : GenericEnumerated3Graph) (n : Nat) (κ : Type) where
  source : ProtectedSource n
  colour : source.Code G → κ

/-- Simultaneous homogeneity for a finite list of independently coloured
OCCURRENCES, not merely distinct source shapes. In particular duplicate
shapes with different colourings remain separate obligations.

This is the exact finite-colouring iteration needed for the upper-bound
argument. It follows from the unconditional ATR theorem with genuine
finite embedding images and the already checked postcomposition laws.
It does not assume diary unavoidability or the final degree formula. -/
theorem actualFiniteAuxRamsey_taskFamily
    (G : GenericEnumerated3Graph) (n : Nat)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (tasks : List (FiniteATRColourTask G n κ)) :
    ∃ (u : Embedding G.graph G.graph)
      (hu : u.AuxTypeRespecting),
      (∀ t < n, u t = t) ∧
      ∀ P ∈ tasks,
        ∃ color : κ, ∀ e : P.source.Code G,
          P.source.FixesPrefix G e →
          P.colour (e.postcompose u hu) = color := by
  induction tasks with
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
      · intro P hmem
        exact False.elim (List.not_mem_nil hmem)
  | cons P rest ih =>
      obtain ⟨g, hg, hfixg, hrest⟩ := ih
      let ρ : P.source.Code G → κ :=
        fun e => P.colour (e.postcompose g hg)
      obtain ⟨h, hh, hfixh, colorP, hcolP⟩ :=
        actualFiniteAuxRamsey_allFinite G
          (n := n) (k := P.source.k) P.source.cut_le
          P.source.picture ρ
      let u : Embedding G.graph G.graph := g.comp h
      have hu : u.AuxTypeRespecting := hg.comp hh
      have hfixu : ∀ t < n, u t = t := by
        intro t ht
        change g (h t) = t
        rw [hfixh t ht, hfixg t ht]
      refine ⟨u, hu, hfixu, ?_⟩
      intro Q hmem
      rcases List.mem_cons.mp hmem with hQP | hQrest
      · subst Q
        refine ⟨colorP, ?_⟩
        intro e he
        have hc : ρ (e.postcompose h hh) = colorP :=
          hcolP e he
        change P.colour ((e.postcompose h hh).postcompose g hg) =
          colorP at hc
        simpa only [FiniteAuxEmbeddingImage.postcompose_comp] using hc
      · obtain ⟨colorQ, hcolQ⟩ := hrest Q hQrest
        refine ⟨colorQ, ?_⟩
        intro e he
        exact protected_colour_persists G n Q.source Q.colour
          g h hg hh hfixh colorQ hcolQ e he

/-- The existing shape-indexed finite-family interface is a special
case. Reusing the occurrence-indexed theorem avoids maintaining two
separate induction/composition arguments. -/
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
  let tasks : List (FiniteATRColourTask G n κ) :=
    family.map (fun A => ⟨A, χ A⟩)
  obtain ⟨u, hu, hfix, hall⟩ :=
    actualFiniteAuxRamsey_taskFamily G n tasks
  refine ⟨u, hu, hfix, ?_⟩
  intro A hA
  have hmem : (⟨A, χ A⟩ : FiniteATRColourTask G n κ) ∈ tasks := by
    exact List.mem_map.mpr ⟨A, hA, rfl⟩
  exact hall ⟨A, χ A⟩ hmem

/-- Regression: two different colours on the SAME source must be
homogenised together. Deduplicating the source shapes would not
establish this statement. -/
theorem actualFiniteAuxRamsey_twoColours_sameSource
    (G : GenericEnumerated3Graph) (n : Nat)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (A : ProtectedSource n)
    (χ₀ χ₁ : A.Code G → κ) :
    ∃ (u : Embedding G.graph G.graph)
      (hu : u.AuxTypeRespecting),
      (∀ t < n, u t = t) ∧
      (∃ color₀ : κ, ∀ e : A.Code G,
        A.FixesPrefix G e →
        χ₀ (e.postcompose u hu) = color₀) ∧
      (∃ color₁ : κ, ∀ e : A.Code G,
        A.FixesPrefix G e →
        χ₁ (e.postcompose u hu) = color₁) := by
  let P : FiniteATRColourTask G n κ := ⟨A, χ₀⟩
  let Q : FiniteATRColourTask G n κ := ⟨A, χ₁⟩
  obtain ⟨u, hu, hfix, hall⟩ :=
    actualFiniteAuxRamsey_taskFamily G n [P, Q]
  obtain ⟨color₀, hcol₀⟩ := hall P (by simp)
  obtain ⟨color₁, hcol₁⟩ := hall Q (by simp)
  exact ⟨u, hu, hfix, ⟨color₀, hcol₀⟩, ⟨color₁, hcol₁⟩⟩

end ATRFiniteDecoder
end ThreeUniformDiaries
