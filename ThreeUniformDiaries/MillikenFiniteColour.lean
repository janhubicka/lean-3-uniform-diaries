import Milliken.MillikenTheorem
import RamseySpace.Ellentuck
import RamseySpace.Standard

/-!
# Finite-colour consequence of the verified homogeneous Milliken theorem

The manuscript uses only the discrete finite-colour consequence of Milliken:
a colouring of one fixed finite strong-subtree height is constant below an
infinite strong subtree.

This file derives exactly that interface from the verified topological
Ramsey-space theorem in `lean-milliken`.
-/

namespace ThreeUniformDiaries

namespace RamseySpace

universe u v w

namespace ApproximationSystem

variable {S : ApproximationSystem.{u, v}}

/-- A colour class determined by one approximation level is Ellentuck-open. -/
theorem isOpen_approxColourClass
    {κ : Type w} (m : Nat) (colour : S.Approx m → κ) (c : κ) :
    @IsOpen S.Point S.ellentuckTopology
      {X | colour (S.approx m X) = c} := by
  rw [S.isOpen_ellentuck_iff]
  intro X hX
  refine ⟨m, S.approx m X, X, ⟨S.le_refl X, rfl⟩, ?_⟩
  intro Y hY
  change colour (S.approx m Y) = c
  change colour (S.approx m X) = c at hX
  rw [hY.2]
  exact hX

end ApproximationSystem

/-- A finite colouring of one approximation level is homogeneous on a
refined basic neighbourhood in every topological Ramsey space. -/
theorem finiteApproximationColouring
    {S : ApproximationSystem.{u, v}}
    (hTR : IsTopologicalRamseySpaceOnBasicNeighborhoods (S := S))
    {κ : Type w} [Fintype κ]
    {n m : Nat} (a : S.Approx n) (A : S.Point)
    (hne : (S.neighborhood a A).Nonempty)
    (colour : S.Approx m → κ) :
    ∃ B, B ∈ S.neighborhood a A ∧
      ∀ X, X ∈ S.neighborhood a B →
        ∀ Y, Y ∈ S.neighborhood a B →
          colour (S.approx m X) = colour (S.approx m Y) := by
  classical
  letI : TopologicalSpace S.Point := S.ellentuckTopology
  let fibre : κ → Set S.Point :=
    fun c => {X | colour (S.approx m X) = c}

  have hdecide :
      ∀ s : Finset κ, ∀ B : S.Point,
        B ∈ S.neighborhood a A →
        ∃ C, C ∈ S.neighborhood a B ∧
          ((∃ c ∈ s, S.neighborhood a C ⊆ fibre c) ∨
            ∀ c ∈ s, Disjoint (S.neighborhood a C) (fibre c)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro B hBA
        refine ⟨B, ⟨S.le_refl B, hBA.2⟩, Or.inr ?_⟩
        simp
    | @insert c s hc ih =>
        intro B hBA
        obtain ⟨C, hCB, hC⟩ := ih B hBA
        rcases hC with hhit | havoid
        · exact ⟨C, hCB, Or.inl (by
            rcases hhit with ⟨d, hd, hsub⟩
            exact ⟨d, Finset.mem_insert_of_mem hd, hsub⟩)⟩
        · have hneC : (S.neighborhood a C).Nonempty :=
            ⟨C, S.le_refl C, hCB.2⟩
          have hopen :
              @BaireMeasurableSet S.Point S.ellentuckTopology (fibre c) :=
            (S.isOpen_approxColourClass m colour c).baireMeasurableSet
          obtain ⟨D, hDC, hhom⟩ :=
            hTR.1 (fibre c) hopen a C hneC
          have hDB : D ∈ S.neighborhood a B :=
            S.neighborhood_mono hCB.1 hDC
          refine ⟨D, hDB, ?_⟩
          rcases hhom with hsub | hdis
          · exact Or.inl ⟨c, Finset.mem_insert_self c s, hsub⟩
          · apply Or.inr
            intro d hd
            rcases Finset.mem_insert.mp hd with hdc | hds
            · subst d
              exact hdis
            · exact (havoid d hds).mono_left
                (S.neighborhood_mono hDC.1)

  obtain ⟨B0, hB0A⟩ := hne
  obtain ⟨B, hBB0, hfinal⟩ :=
    hdecide Finset.univ B0 hB0A
  have hBA : B ∈ S.neighborhood a A :=
    S.neighborhood_mono hB0A.1 hBB0
  rcases hfinal with hhit | havoid
  · rcases hhit with ⟨c, _, hsub⟩
    refine ⟨B, hBA, ?_⟩
    intro X hX Y hY
    exact (hsub hX).trans (hsub hY).symm
  · exfalso
    let c : κ := colour (S.approx m B)
    have hdis := havoid c (Finset.mem_univ c)
    have hB : B ∈ S.neighborhood a B :=
      ⟨S.le_refl B, hBB0.2⟩
    have hBc : B ∈ fibre c := rfl
    exact Set.disjoint_left.1 hdis hB hBc

end RamseySpace

open Milliken

/-- The concrete finite-colour formulation of homogeneous-tree Milliken.

Below the returned strong embedding `B`, every realized height-`m`
approximation has the same colour. -/
theorem homogeneousMillikenFiniteColouring
    {ι : Type u} [Finite ι] [Nonempty ι]
    {κ : Type v} [Fintype κ]
    (m : Nat)
    (colour : StrongTreeSpace.Approx ι m → κ) :
    ∃ B : StrongEmbedding ι,
      ∀ X Y : StrongEmbedding ι,
        StrongTreeSpace.le ι X B →
        StrongTreeSpace.le ι Y B →
        colour (StrongTreeSpace.approx ι m X) =
          colour (StrongTreeSpace.approx ι m Y) := by
  let S := StrongTreeSpace.approximationSystem ι
  have hne :
      (S.neighborhood (StrongTreeSpace.empty ι)
        (StrongEmbedding.id : StrongEmbedding ι)).Nonempty := by
    refine ⟨StrongEmbedding.id, ?_⟩
    exact ⟨StrongTreeSpace.le_refl ι _, StrongTreeSpace.approx_zero _ _⟩
  obtain ⟨B, hB, hhom⟩ :=
    RamseySpace.finiteApproximationColouring
      (Milliken.Chapter6.milliken_onBasicNeighborhoods (ι := ι))
      (StrongTreeSpace.empty ι)
      (StrongEmbedding.id : StrongEmbedding ι)
      hne colour
  refine ⟨B, ?_⟩
  intro X Y hXB hYB
  have hX :
      X ∈ S.neighborhood (StrongTreeSpace.empty ι) B :=
    ⟨hXB, StrongTreeSpace.approx_zero ι X⟩
  have hY :
      Y ∈ S.neighborhood (StrongTreeSpace.empty ι) B :=
    ⟨hYB, StrongTreeSpace.approx_zero ι Y⟩
  exact hhom X hX Y hY

end ThreeUniformDiaries
