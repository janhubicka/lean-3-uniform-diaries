import ThreeUniformDiaries.DiaryFiniteATRFamily

/-!
# Track C: an honest finite-palette consequence of auxiliary Ramsey

This file supplies the quantified finite-colour conclusion needed for
a potential upper-bound argument.  The independent, fully proved input
is `actualFiniteAuxRamsey_finiteFamily`: it homogenises finitely many
possibly different finite source *auxiliary-type-respecting* embedding
codes inside one refined enumerated generic hypergraph.

There is one colour for each source occurrence in the given list.
The resulting list of possible colours is **no longer** than the
source list.  Repetitions are harmless; the conclusion does not
identify labelled embeddings with unlabelled copies.

Crucially, this is NOT the manuscript's upper-bound theorem.
The missing geometric interface must still show that every embedding
of A into the refined ambient hypergraph is represented by one
of the genuinely auxiliary-type-respecting finite codes for its
diary.  A separate countable diary-unavoidability step is needed
to place the refined generic range inside a diary copy.  Neither
assumption is smuggled into the finite Ramsey statement.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- Finite-family ATR yields an explicit palette list of precisely
`family.length` entries.  Each source code receives a colour on
postcomposition with ONE common prefix-fixing auxiliary-type-
respecting generic self-embedding, and that colour belongs to
the palette.  No unavoidability, diary Ramsey, or assumed
classification of all copies of an arbitrary A is used. -/
theorem actualFiniteAuxRamsey_finiteFamily_palette
    (G : GenericEnumerated3Graph) (n : Nat)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : ∀ A : ProtectedSource n, A.Code G → κ)
    (family : List (ProtectedSource n)) :
    ∃ (u : Embedding G.graph G.graph)
      (hu : u.AuxTypeRespecting),
      (∀ t < n, u t = t) ∧
      ∃ palette : List κ,
        palette.length = family.length ∧
        ∀ A ∈ family, ∀ e : A.Code G,
          A.FixesPrefix G e →
          χ A (e.postcompose u hu) ∈ palette := by
  classical
  obtain ⟨u, hu, hfix, hcolor⟩ :=
    actualFiniteAuxRamsey_finiteFamily G n χ family
  let selected : ProtectedSource n → κ := fun A =>
    if hA : A ∈ family then Classical.choose (hcolor A hA)
    else Classical.choice inferInstance
  refine ⟨u, hu, hfix, family.map selected, by simp, ?_⟩
  intro A hA e he
  have hc : χ A (e.postcompose u hu) =
      Classical.choose (hcolor A hA) :=
    Classical.choose_spec (hcolor A hA) e he
  have hs : selected A = Classical.choose (hcolor A hA) := by
    simp [selected, hA]
  have hm : selected A ∈ family.map selected :=
    List.mem_map.mpr ⟨A, hA, rfl⟩
  have hχ : χ A (e.postcompose u hu) = selected A :=
    hc.trans hs.symm
  rw [hχ]
  exact hm

/-- At cut zero every finite source embedding fixes the empty
prefix, so no artificial fixed-prefix hypothesis survives.
This is the direct finite-list interface for an upper-bound proof
after the source diaries have been correctly classified. -/
theorem actualFiniteAuxRamsey_zeroCut_palette
    (G : GenericEnumerated3Graph)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : ∀ A : ProtectedSource 0, A.Code G → κ)
    (family : List (ProtectedSource 0)) :
    ∃ (u : Embedding G.graph G.graph)
      (hu : u.AuxTypeRespecting),
      ∃ palette : List κ,
        palette.length = family.length ∧
        ∀ A ∈ family, ∀ e : A.Code G,
          χ A (e.postcompose u hu) ∈ palette := by
  obtain ⟨u, hu, _, palette, hlen, hcolour⟩ :=
    actualFiniteAuxRamsey_finiteFamily_palette G 0 χ family
  refine ⟨u, hu, palette, hlen, ?_⟩
  intro A hA e
  exact hcolour A hA e (by intro i hi; omega)

end ATRFiniteDecoder
end ThreeUniformDiaries
