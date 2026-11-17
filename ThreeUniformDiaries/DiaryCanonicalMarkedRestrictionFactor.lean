import ThreeUniformDiaries.DiaryLowerCanonicalMarkedColour
import ThreeUniformDiaries.DiaryCountableCofinalFiniteSupports

/-!
# Canonical marked-diary restriction: first verified interfaces

This module isolates the two pieces that can be proved without assuming
that the eventual marked-diary restriction map already exists.

* Every genuine selected subtuple has its complete finite S1/S2 generated
  support INSIDE the larger tuple's complete support, even when the label
  map is not increasing.
* A surjective large colour admits a unique restriction map to a small
  colour precisely when the small colour is constant on each fibre of
  the large colour. We prove the complete identity/composition laws.

The remaining diary-specific task is the FIBRE CONSTANCY assertion for
canonicalMarkedDiaryColour, not the elementary extraction of rho from
fibre constancy. No artificial assumptions about finite-diary
selfembedding or countable diary unavoidability enter these theorems.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open DiaryLeafPriority

/-- Selecting ANY subfamily of labelled leaves, without assuming
that the label injection is numerically increasing, places its full
S1/S2 leaf-meet support inside the larger labelled family's support.

No diary axioms or injectivity of the selection map are needed. -/
theorem finiteLeafMeetSupport_subtuple_subset
    (K : Ordered3Graph Nat)
    {a b : Nat} (v : Fin a → Nat) (i : Fin b → Fin a) :
    finiteLeafMeetSupport K
        ((Finset.univ : Finset (Fin b)).image (fun j => v (i j))) ⊆
      finiteLeafMeetSupport K
        ((Finset.univ : Finset (Fin a)).image v) := by
  apply finiteLeafMeetSupport_mono K
  intro x hx
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨i j, Finset.mem_univ _, rfl⟩

/-- An exact, surjective large colour determines a candidate
restriction by choosing one representative in each fibre. The
fibre-constancy hypothesis is deliberately displayed in full.

This construction is abstract; its later diary instantiation must
verify that equality of complete marked A-sources implies equality
of the marked B-source of every selected B-subcopy. -/
noncomputable def colourRestrictionOfFibres
    {A B X : Type*}
    (large : X → A) (small : X → B)
    (hLarge : Function.Surjective large)
    (_hFibre : ∀ x y : X, large x = large y → small x = small y) :
    A → B :=
  fun a => small (Classical.choose (hLarge a))

/-- Every restriction constructed from fibre constancy gives the
right colour at EVERY actual realization, not just at the
representatives chosen to define the restriction. -/
theorem colourRestrictionOfFibres_apply
    {A B X : Type*}
    (large : X → A) (small : X → B)
    (hLarge : Function.Surjective large)
    (hFibre : ∀ x y : X, large x = large y → small x = small y)
    (x : X) :
    colourRestrictionOfFibres large small hLarge hFibre (large x) =
      small x := by
  unfold colourRestrictionOfFibres
  exact hFibre (Classical.choose (hLarge (large x))) x
    (Classical.choose_spec (hLarge (large x)))

/-- A restriction factorization is UNIQUE if the larger colour
uses its whole claimed palette. -/
theorem colourRestrictionOfFibres_unique
    {A B X : Type*}
    (large : X → A) (small : X → B)
    (hLarge : Function.Surjective large)
    (hFibre : ∀ x y : X, large x = large y → small x = small y)
    (r : A → B)
    (hr : ∀ x : X, r (large x) = small x) :
    r = colourRestrictionOfFibres large small hLarge hFibre := by
  funext a
  obtain ⟨x, rfl⟩ := hLarge a
  exact (hr x).trans
    (colourRestrictionOfFibres_apply large small hLarge hFibre x).symm

/-- Such a factorization exists iff the smaller colour is constant
on the fibres of the larger colour. There is no need to assume the
small colour surjective. -/
theorem colourRestriction_existsUnique_iff_fibre
    {A B X : Type*}
    (large : X → A) (small : X → B)
    (hLarge : Function.Surjective large) :
    (∃! r : A → B, ∀ x : X, r (large x) = small x) ↔
      (∀ x y : X, large x = large y → small x = small y) := by
  constructor
  · rintro ⟨r, hr, _⟩ x y hxy
    calc
      small x = r (large x) := (hr x).symm
      _ = r (large y) := congrArg r hxy
      _ = small y := hr y
  · intro hFibre
    refine ⟨colourRestrictionOfFibres large small hLarge hFibre, ?_, ?_⟩
    · intro x
      exact colourRestrictionOfFibres_apply large small hLarge hFibre x
    · intro r hr
      exact colourRestrictionOfFibres_unique
        large small hLarge hFibre r hr

/-- Restriction to a colour itself is the identity. -/
theorem colourRestrictionOfFibres_id
    {A X : Type*} (large : X → A)
    (hLarge : Function.Surjective large) :
    colourRestrictionOfFibres large large hLarge
        (fun _ _ h => h) = id := by
  exact (colourRestrictionOfFibres_unique
    large large hLarge (fun _ _ h => h) id (fun _ => rfl)).symm

/-- Canonical restrictions compose once the corresponding
fibre-constancy statements are known. This is the exact
contravariant composition law needed for restriction along
embeddings C -> B -> A. -/
theorem colourRestrictionOfFibres_comp
    {A B C X : Type*}
    (large : X → A) (medium : X → B) (small : X → C)
    (hLarge : Function.Surjective large)
    (hMedium : Function.Surjective medium)
    (hLM : ∀ x y : X, large x = large y → medium x = medium y)
    (hMS : ∀ x y : X, medium x = medium y → small x = small y) :
    colourRestrictionOfFibres large small hLarge
        (fun x y h => hMS x y (hLM x y h)) =
      (colourRestrictionOfFibres medium small hMedium hMS) ∘
        (colourRestrictionOfFibres large medium hLarge hLM) := by
  funext a
  obtain ⟨x, rfl⟩ := hLarge a
  simp only [Function.comp_apply]
  rw [colourRestrictionOfFibres_apply large small hLarge
        (fun x y h => hMS x y (hLM x y h)) x,
      colourRestrictionOfFibres_apply large medium hLarge hLM x,
      colourRestrictionOfFibres_apply medium small hMedium hMS x]

end ATRFiniteDecoder
end ThreeUniformDiaries
