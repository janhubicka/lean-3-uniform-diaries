import ThreeUniformDiaries.CoherentSharpColoursBRSAbstract

/-!
# Abstract big Ramsey relational expansion from coherent sharp colours

An abstract coherent finite colour family defines ONE relation symbol
for each finite enumerated induced source and palette colour. The
complete induced expansion profile of a finite A-copy remembers
exactly its top A-colour, and no more.

We prove (1) a bijection between real induced expansion types
and the finite A-colour palette and (2) unavoidability of every
expansion type in EVERY induced selfcopy of the underlying U.
The resulting finite expansion-type count is exactly the colour
palette size. If those palettes realize the sharp big Ramsey
degrees, this construction satisfies the defining two BRS
properties. Countability of the expansion language is checked
separately below and does not require a finite language.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder
namespace CoherentFiniteColourSystem

open _root_.ThreeUniformDiaries.Ordered3Graph

variable {U : Ordered3Graph Nat} (C : CoherentFiniteColourSystem U)

noncomputable instance paletteFintype {a : Nat} (A : EnumNode a) :
    Fintype (C.Palette a A) := by
  classical
  letI : Finite (C.Palette a A) := C.finitePalette A
  exact Fintype.ofFinite _

/-- Genuine finite expansion types are the FULL induced relation
profiles actually realized by some finite induced A-embedding. -/
abbrev RealizedProfile {a : Nat} (A : EnumNode a) : Type :=
  {p : C.Profile A //
    ∃ v : GenuineFiniteEmbeddings A U, C.inducedProfile A v = p}

/-- Select the realized full expansion type associated to d by
choosing one genuine A-copy of colour d. Coherence guarantees that
the result is independent of the chosen copy. -/
noncomputable def realizedProfileOfColour {a : Nat} (A : EnumNode a)
    (d : C.Palette a A) : C.RealizedProfile A := by
  classical
  let v : GenuineFiniteEmbeddings A U :=
    Classical.choose (C.surj A d)
  exact ⟨C.inducedProfile A v, ⟨v,rfl⟩⟩

/-- Distinct top colours give distinct COMPLETE finite expansion
types; the full A-arity relation R_(A,d) witnesses distinction. -/
theorem realizedProfileOfColour_injective {a : Nat} (A : EnumNode a) :
    Function.Injective (C.realizedProfileOfColour A) := by
  classical
  intro d e h
  have hp := congrArg Subtype.val h
  change C.inducedProfile A (Classical.choose (C.surj A d)) =
      C.inducedProfile A (Classical.choose (C.surj A e)) at hp
  have hc := (C.inducedProfile_eq_iff_colour_eq A _ _).mp hp
  calc
    d = C.colour A (Classical.choose (C.surj A d)) :=
      (Classical.choose_spec (C.surj A d)).symm
    _ = C.colour A (Classical.choose (C.surj A e)) := hc
    _ = e := Classical.choose_spec (C.surj A e)

/-- Every realized complete finite expansion type comes from
a single canonical top A-colour. -/
theorem realizedProfileOfColour_surjective {a : Nat} (A : EnumNode a) :
    Function.Surjective (C.realizedProfileOfColour A) := by
  classical
  intro p
  obtain ⟨v,hv⟩ := p.property
  let d : C.Palette a A := C.colour A v
  refine ⟨d, ?_⟩
  apply Subtype.ext
  change C.inducedProfile A (Classical.choose (C.surj A d)) = p.val
  calc
    C.inducedProfile A (Classical.choose (C.surj A d)) =
        C.inducedProfile A v :=
      (C.inducedProfile_eq_iff_colour_eq A _ _).mpr
        (Classical.choose_spec (C.surj A d))
    _ = p.val := hv

/-- LITERAL bijection between the finite A-colour palette and
the induced expansion TYPES of the abstract relational expansion. -/
noncomputable def paletteEquivRealizedProfiles {a : Nat} (A : EnumNode a) :
    C.Palette a A ≃ C.RealizedProfile A :=
  Equiv.ofBijective (C.realizedProfileOfColour A)
    ⟨C.realizedProfileOfColour_injective A,
      C.realizedProfileOfColour_surjective A⟩

/-- The realized expansion profile of A has exactly as many
types as the finite A-colour palette. This is the numerical
portion of the abstract BRS assembly, independent of how
the colours were originally constructed. -/
noncomputable instance realizedProfileFintype {a : Nat} (A : EnumNode a) :
    Fintype (C.RealizedProfile A) := by
  classical
  exact Fintype.ofEquiv (C.Palette a A) (C.paletteEquivRealizedProfiles A)

theorem realizedProfile_card {a : Nat} (A : EnumNode a) :
    Fintype.card (C.RealizedProfile A) =
      Fintype.card (C.Palette a A) := by
  classical
  exact Fintype.card_congr (C.paletteEquivRealizedProfiles A).symm

/-- EVERY complete finite induced expansion type is unavoidable
in EVERY unordered induced U-selfcopy, provided every individual
canonical A-colour is unavoidable there. No countable diary
unavoidability or expansion-Ramsey theorem is assumed. -/
theorem realizedProfile_unavoidable {a : Nat} (A : EnumNode a)
    (p : C.RealizedProfile A) (w : UnorderedEmbedding U U) :
    ∃ v : GenuineFiniteEmbeddings A U,
      C.inducedProfile A (v.postcompose w) = p.val := by
  obtain ⟨v₀,hv₀⟩ := p.property
  obtain ⟨v,hv⟩ := C.unavoidable A w (C.colour A v₀)
  refine ⟨v, ?_⟩
  calc
    C.inducedProfile A (v.postcompose w) =
        C.inducedProfile A v₀ :=
      (C.inducedProfile_eq_iff_colour_eq A _ _).mpr hv
    _ = p.val := hv₀

end CoherentFiniteColourSystem
end ATRFiniteDecoder
end ThreeUniformDiaries
