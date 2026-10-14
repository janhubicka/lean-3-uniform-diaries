import ThreeUniformDiaries.DiaryFiniteATRFamily

/-!
# Combining finite avoidance with simultaneous finite ATR stabilisation

The stage construction in the diary lower bound first obtains a
prefix-fixing aux-type-respecting refinement g that sends every
vertex of the tail past a finite forbidden target bound M. It then
homogenises a finite family of singleton and pointed-pair envelope
colours by another prefix-fixing refinement h.

This module proves that the COMPOSITE g ∘ h retains the avoidance
of M and simultaneously homogenises every finite source colour.
The external map F is arbitrary: this lemma does not assume F is
monotone, nor does it require injection once avoidance has been
established. No source continuation outside its actual finite
vertices is part of any colouring.

The proof is independent of the way avoidance was obtained and
of the particular finite colour. It is the algebraic glue between
generic finite avoidance and the type/auxiliary/orientation masks.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- Every strictly increasing map on Nat lies pointwise at or
above the identity. This is needed only to show that later
refinements keep the source tail inside itself. -/
theorem strictMono_nat_self_le
    (f : Nat → Nat) (hf : StrictMono f) :
    ∀ t, t ≤ f t := by
  intro t
  induction t with
  | zero =>
      omega
  | succ t ih =>
      have hstep : f t < f (t+1) := hf (Nat.lt_succ_self t)
      omega

/-- A second finite-family ATR refinement does not destroy the
earlier finite-avoidance condition. Its composite with the first
refinement also stabilises the specified finite source colour for
every family member simultaneously.

The supplied avoidance is the actual geometric result at this
cut, while the finite-family Ramsey theorem constructs the
additional colour-homogenising refinement. -/
theorem finiteAvoidance_and_finiteFamilyStabilisation
    (G : GenericEnumerated3Graph) (n : Nat)
    (F : Nat → Nat) (M : Nat)
    (g : Embedding G.graph G.graph)
    (hg : g.AuxTypeRespecting)
    (hfixg : ∀ t < n, g t = t)
    (havoid : ∀ a, n ≤ a → M < F (g a))
    {κ : Type} [Fintype κ] [Nonempty κ]
    (χ : ∀ A : ProtectedSource n, A.Code G → κ)
    (family : List (ProtectedSource n)) :
    ∃ (u : Embedding G.graph G.graph)
      (hu : u.AuxTypeRespecting),
      (∀ t < n, u t = t) ∧
      (∀ a, n ≤ a → M < F (u a)) ∧
      ∀ A ∈ family,
        ∃ color : κ, ∀ e : A.Code G,
          A.FixesPrefix G e →
          χ A (e.postcompose u hu) = color := by
  let pulled : ∀ A : ProtectedSource n, A.Code G → κ :=
    fun A e => χ A (e.postcompose g hg)
  obtain ⟨h, hh, hfixh, hcolors⟩ :=
    actualFiniteAuxRamsey_finiteFamily G n pulled family
  let u : Embedding G.graph G.graph := g.comp h
  have hu : u.AuxTypeRespecting := hg.comp hh
  have hfixu : ∀ t < n, u t = t := by
    intro t ht
    change g (h t) = t
    rw [hfixh t ht, hfixg t ht]
  have hAvoidU : ∀ a, n ≤ a → M < F (u a) := by
    intro a ha
    have hTail : n ≤ h a :=
      ha.trans (strictMono_nat_self_le h.toFun h.strictMono a)
    have hResult := havoid (h a) hTail
    change M < F (g (h a)) at hResult
    exact hResult
  refine ⟨u, hu, hfixu, hAvoidU, ?_⟩
  intro A hmem
  obtain ⟨color, hcolor⟩ := hcolors A hmem
  refine ⟨color, ?_⟩
  intro e he
  have hstep := hcolor e he
  change χ A ((e.postcompose h hh).postcompose g hg) = color at hstep
  simpa only [FiniteAuxEmbeddingImage.postcompose_comp] using hstep

end ATRFiniteDecoder
end ThreeUniformDiaries
