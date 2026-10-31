import ThreeUniformDiaries.DiaryFiniteATRFamily

/-!
# Track C: transferring finite palettes from copies to labelled embeddings

This file isolates the exact finite combinatorial calculation behind
the `|Aut(A)|` factor in the big Ramsey degree formula.

A finite family of *vector colours*, with one coordinate for each
possible labelling, yields at most

    (number of vector colours) * (number of labellings)

individual embedding colours.  No Ramsey, diary, or counting
hypothesis is needed for this finite calculation.

The second theorem states the exact additional input required when
unlabelled copies are represented by a chosen labelled embedding:
every selected embedding must factor through its chosen representative
and a label (eventually an automorphism of A).  That factorization is
an EXPLICIT assumption, not a claim already proved for 3-hypergraphs.

In particular, these two statements do NOT prove that the diary count
is the number of distinct vector colours, nor do they prove countable
diary unavoidability or the upper bound in the manuscript.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

/-- A finite palette of label-indexed colour vectors gives a palette
of individual colours of cardinality at most the number of vectors
times the number of possible labels.  The source `X` need not be
finite.  Every source object's colour is one coordinate of its
associated vector; that vector is assumed to belong to the palette. -/
theorem finite_vector_palette_transfer
    {X Label Colour : Type}
    [Fintype Label]
    (palette : Finset (Label → Colour))
    (vector : X → Label → Colour)
    (label : X → Label)
    (colour : X → Colour)
    (hvector : ∀ x : X, vector x ∈ palette)
    (hcolour : ∀ x : X, colour x = vector x (label x)) :
    ∃ used : Finset Colour,
      used.card ≤ palette.card * Fintype.card Label ∧
      ∀ x : X, colour x ∈ used := by
  classical
  let used : Finset Colour :=
    (palette.product (Finset.univ : Finset Label)).image
      (fun p => p.1 p.2)
  refine ⟨used, ?_, ?_⟩
  · calc
      used.card ≤
          (palette.product (Finset.univ : Finset Label)).card :=
        Finset.card_image_le
      _ = palette.card * Fintype.card Label := by simp
  · intro x
    have hpair : (vector x, label x) ∈
        palette.product (Finset.univ : Finset Label) :=
      Finset.mem_product.mpr ⟨hvector x, Finset.mem_univ _⟩
    have hmem : vector x (label x) ∈ used :=
      Finset.mem_image.mpr ⟨(vector x, label x), hpair, rfl⟩
    rw [hcolour x]
    exact hmem

/-- A precise abstract labelled/unlabelled-copy transfer.

The map `copy` forgets labels.  The map `representative` labels
each copy with a chosen representative and an automorphism/label
coordinate.  For selected embeddings, `hrepresentative` requires
that this reconstruction be EXACT.  If every selected copy has
its complete label-vector colour in a fixed finite palette,
then the colours of all selected labelled embeddings lie in
a palette of cardinality at most `palette.card * card Label`.

The reconstruction hypothesis is the mathematical place where
one later has to prove that the label type is precisely Aut(A),
rather than all vertex permutations or an unspecified set. -/
theorem labelled_colour_palette_of_copy_vectors
    {Emb Copy Label Colour : Type}
    [Fintype Label]
    (colour : Emb → Colour)
    (copy : Emb → Copy)
    (representative : Copy → Label → Emb)
    (label : Emb → Label)
    (selected : Emb → Prop)
    (hrepresentative : ∀ e : Emb, selected e →
      representative (copy e) (label e) = e)
    (palette : Finset (Label → Colour))
    (hpalette : ∀ e : Emb, selected e →
      (fun a : Label => colour (representative (copy e) a)) ∈ palette) :
    ∃ used : Finset Colour,
      used.card ≤ palette.card * Fintype.card Label ∧
      ∀ e : Emb, selected e → colour e ∈ used := by
  classical
  let X := { e : Emb // selected e }
  let v : X → Label → Colour :=
    fun e a => colour (representative (copy e.1) a)
  let l : X → Label := fun e => label e.1
  let c : X → Colour := fun e => colour e.1
  have hv : ∀ e : X, v e ∈ palette := by
    intro e
    exact hpalette e.1 e.2
  have hc : ∀ e : X, c e = v e (l e) := by
    intro e
    dsimp [c, v, l]
    rw [hrepresentative e.1 e.2]
  obtain ⟨used, hcard, hmem⟩ :=
    finite_vector_palette_transfer palette v l c hv hc
  refine ⟨used, hcard, ?_⟩
  intro e he
  exact hmem ⟨e, he⟩

end ATRFiniteDecoder
end ThreeUniformDiaries
