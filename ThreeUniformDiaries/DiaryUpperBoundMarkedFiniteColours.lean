import ThreeUniformDiaries.DiaryFiniteATRFamily

/-!
# Track A: marked finite ATR colour palette for diary upper bounds

Finite source occurrences with distinct colourings are handled by
the shared FiniteATRColourTask/actualFiniteAuxRamsey_taskFamily
interface in DiaryFiniteATRFamily (Track B PR #977). There is
no second copy of the finite Ramsey induction in this module.

The sole new ingredient is the explicit finite *marking* of the
labelled leaves whose image tuple is to be coloured. Each colour
depends only on the genuine finite source images, never on the
infinite zero-extension tail.

The marked palette theorem is conditional on an independently
proved factorisation of actual diary A-copies through these marked
finite ATR source shapes. It does not assert this missing premise.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- Compatibility name for the canonical occurrence-indexed task
interface, rather than a separately maintained structure. -/
abbrev ColouredProtectedSource
    (G : GenericEnumerated3Graph) (n : Nat)
    (κ : Type) := FiniteATRColourTask G n κ

/-- The common occurrence-indexed Ramsey theorem is proved once
in DiaryFiniteATRFamily, including duplicate source shapes. -/
theorem actualFiniteAuxRamsey_colouredTasks
    (G : GenericEnumerated3Graph) (n : Nat)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (tasks : List (ColouredProtectedSource G n κ)) :
    ∃ (u : Embedding G.graph G.graph)
      (hu : u.AuxTypeRespecting),
      (∀ t < n, u t = t) ∧
      ∀ T ∈ tasks,
        ∃ colour : κ, ∀ e : T.source.Code G,
          T.source.FixesPrefix G e →
          T.colour (e.postcompose u hu) = colour :=
  actualFiniteAuxRamsey_taskFamily G n tasks

/-- A finite enumerated source together with positions of the
labelled vertices whose images are to be coloured. The marked
positions will be leaves in the eventual diary application, but
that condition is NOT assumed by this generic ATR lemma. -/
structure MarkedFiniteSource (n a : Nat) where
  source : ProtectedSource n
  marked : Fin a → Fin (source.k + 1)

/-- Pull back a colouring on labelled target tuples through the
actual selected finite-source images and an arbitrary outer map.
No monotonicity of the outer map is needed for this formal step. -/
def MarkedFiniteSource.asColourTask
    {n a : Nat} (S : MarkedFiniteSource n a)
    (G : GenericEnumerated3Graph)
    {κ : Type} (ψ : Nat → Nat)
    (χ : (Fin a → Nat) → κ) :
    ColouredProtectedSource G n κ where
  source := S.source
  colour := fun e =>
    χ (fun i => ψ (e.image (S.marked i)))

/-- ONE aux-type-respecting self-embedding homogenises all
labelled-tuple colourings determined by a finite list of marked
sources, including duplicate source shapes with distinct markings. -/
theorem actualFiniteAuxRamsey_markedFamily
    (G : GenericEnumerated3Graph) (n a : Nat)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (ψ : Nat → Nat) (χ : (Fin a → Nat) → κ)
    (family : List (MarkedFiniteSource n a)) :
    ∃ (u : Embedding G.graph G.graph)
      (hu : u.AuxTypeRespecting),
      (∀ t < n, u t = t) ∧
      ∀ S ∈ family,
        ∃ colour : κ, ∀ e : S.source.Code G,
          S.source.FixesPrefix G e →
          χ (fun i => ψ (u (e.image (S.marked i)))) = colour := by
  let tasks : List (ColouredProtectedSource G n κ) :=
    family.map (fun S => S.asColourTask G ψ χ)
  obtain ⟨u, hu, hfix, hAll⟩ :=
    actualFiniteAuxRamsey_colouredTasks G n tasks
  refine ⟨u, hu, hfix, ?_⟩
  intro S hmem
  have hmem' : S.asColourTask G ψ χ ∈ tasks := by
    change S.asColourTask G ψ χ ∈
      family.map (fun T => T.asColourTask G ψ χ)
    exact List.mem_map.mpr ⟨S, hmem, rfl⟩
  obtain ⟨colour, hcol⟩ :=
    hAll (S.asColourTask G ψ χ) hmem'
  refine ⟨colour, ?_⟩
  intro e he
  have hc := hcol e he
  change χ (fun i =>
    ψ ((e.postcompose u hu).image (S.marked i))) = colour at hc
  simpa only [FiniteAuxEmbeddingImage.postcompose_apply] using hc

/-- An explicit colour palette of length at most the number of
marked source tasks, provided each input tuple factors through one
of their genuine finite ATR codes. This is the noncircular
COMBINATORIAL component of the big-Ramsey upper bound.

The factorisation premise is intentional: the missing diary-envelope
classification must later supply it for the copies of a fixed A.
-/
theorem actualFiniteAuxRamsey_markedPalette
    (G : GenericEnumerated3Graph) (n a : Nat)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (ψ : Nat → Nat) (χ : (Fin a → Nat) → κ)
    (family : List (MarkedFiniteSource n a)) :
    ∃ (u : Embedding G.graph G.graph)
      (hu : u.AuxTypeRespecting),
      (∀ t < n, u t = t) ∧
      ∃ palette : List κ,
        palette.length = family.length ∧
        ∀ v : Fin a → Nat,
          (∃ S ∈ family, ∃ e : S.source.Code G,
            S.source.FixesPrefix G e ∧
            ∀ i, v i = e.image (S.marked i)) →
          χ (fun i => ψ (u (v i))) ∈ palette := by
  classical
  obtain ⟨u, hu, hfix, hAll⟩ :=
    actualFiniteAuxRamsey_markedFamily G n a ψ χ family
  let select : MarkedFiniteSource n a → κ :=
    fun S =>
      if hS : S ∈ family then Classical.choose (hAll S hS)
      else Classical.choice (inferInstance : Nonempty κ)
  refine ⟨u, hu, hfix, family.map select, by simp, ?_⟩
  intro v hfactor
  obtain ⟨S, hS, e, he, hv⟩ := hfactor
  have hcolour :
      χ (fun i => ψ (u (e.image (S.marked i)))) =
        Classical.choose (hAll S hS) :=
    Classical.choose_spec (hAll S hS) e he
  have hselect : select S = Classical.choose (hAll S hS) := by
    simp only [select, dif_pos hS]
  have hfunctions :
      (fun i => ψ (u (v i))) =
        (fun i => ψ (u (e.image (S.marked i)))) := by
    funext i
    exact congrArg (fun x : Nat => ψ (u x)) (hv i)
  have hvalue : χ (fun i => ψ (u (v i))) = select S :=
    ((congrArg χ hfunctions).trans hcolour).trans hselect.symm
  rw [hvalue]
  exact List.mem_map.mpr ⟨S, hS, rfl⟩

/-- At the unprotected cut n=0 there is NO extra fixed-prefix
condition in the factorisation hypothesis: this is the exact
finite-colouring form wanted for the upper-bound iteration. -/
theorem actualFiniteAuxRamsey_markedPalette_zero
    (G : GenericEnumerated3Graph) (a : Nat)
    {κ : Type} [Fintype κ] [Nonempty κ]
    (ψ : Nat → Nat) (χ : (Fin a → Nat) → κ)
    (family : List (MarkedFiniteSource 0 a)) :
    ∃ (u : Embedding G.graph G.graph)
      (hu : u.AuxTypeRespecting),
      ∃ palette : List κ,
        palette.length = family.length ∧
        ∀ v : Fin a → Nat,
          (∃ S ∈ family, ∃ e : S.source.Code G,
            ∀ i, v i = e.image (S.marked i)) →
          χ (fun i => ψ (u (v i))) ∈ palette := by
  obtain ⟨u, hu, _, palette, hlength, hbound⟩ :=
    actualFiniteAuxRamsey_markedPalette G 0 a ψ χ family
  refine ⟨u, hu, palette, hlength, ?_⟩
  intro v hfactor
  apply hbound v
  obtain ⟨S, hS, e, he⟩ := hfactor
  refine ⟨S, hS, e, ?_, he⟩
  intro i hi
  omega

end ATRFiniteDecoder
end ThreeUniformDiaries
