import ThreeUniformDiaries.DiaryUniformEnvelopeStage
import ThreeUniformDiaries.DiaryAllSingletonAvoidance
import ThreeUniformDiaries.DiaryStageAvoidanceComposition

/-!
# One complete finite stage of diary type stabilisation

The proof of the diary lower bound starts with an arbitrary injective
outer map F (which is NOT assumed order-preserving). At a protected
cut n, one first applies generic/ATR finite avoidance to move ALL
tail vertices beyond a forbidden outer-image bound M. One then
homogenises all singleton and auxiliary-pair/orientation colours on
all finite one-, two- and three-tail envelope sources.

The finite universal shape list, the all-singleton avoidance theorem
and the persistence of avoidance under prefix-fixed ATR refinements
are already separate verified interfaces. This file composes them
into ONE genuine aux-type-respecting generic self-embedding.

The second theorem chooses M = F(n-1), proving that the new composite
outer map becomes increasing on the first n+1 vertices whenever F
was increasing on the first n vertices. This is the one-stage order
induction required in the manuscript's stage-by-stage construction.

The full countable coherent sequence and the claim that every
pointed diary pair corresponds to its canonical finite code are
separate obligations; no completed lower bound is claimed here.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- At any protected source cut n and arbitrary fixed target cut N,
one prefix-fixed aux-type-respecting refinement simultaneously
avoids a forbidden outer-image interval on ALL tail vertices and
homogenises full singleton/pair/lexicographic finite colours on
ALL possible ATR source shapes with at most three exterior vertices.

No order assumption on F is made, only injectivity. -/
theorem actualFiniteAuxRamsey_completeStage
    (G : GenericEnumerated3Graph) (n : Nat)
    (K : Ordered3Graph Nat)
    (F : Nat → Nat) (hF : Function.Injective F)
    (M N : Nat) :
    ∃ (u : Embedding G.graph G.graph)
      (hu : u.AuxTypeRespecting),
      (∀ t < n, u t = t) ∧
      (∀ a, n ≤ a → M < F (u a)) ∧
      ∀ A ∈ smallSourceUniverse n,
        ∃ color : FullEnvelopeColour N,
          ∀ e : A.Code G, A.FixesPrefix G e →
            fullEnvelopeColour K F N A
              (e.postcompose u hu) = color := by
  obtain ⟨g, hg, hfixg, havoid⟩ :=
    G.exists_prefix_fixed_avoiding_refinement n F hF M
  let χ : ∀ A : ProtectedSource n, A.Code G →
      FullEnvelopeColour N :=
    fun A e => fullEnvelopeColour K F N A e
  exact finiteAvoidance_and_finiteFamilyStabilisation
    G n F M g hg hfixg havoid χ (smallSourceUniverse n)

/-- The complete stage extends an already strictly increasing outer
prefix from n vertices to n+1 while keeping the first n source
vertices fixed and retaining every finite type/orientation colour.
The finite target cut N may be chosen separately, e.g.
N = F(n-1)+1 as in the manuscript's construction. -/
theorem actualFiniteAuxRamsey_extendOrderedPrefix
    (G : GenericEnumerated3Graph)
    (n : Nat) (hn : 0 < n)
    (K : Ordered3Graph Nat)
    (F : Nat → Nat) (hF : Function.Injective F)
    (hprefix : ∀ a b, a < b → b < n → F a < F b)
    (N : Nat) :
    ∃ (u : Embedding G.graph G.graph)
      (hu : u.AuxTypeRespecting),
      (∀ t < n, u t = t) ∧
      (∀ a b, a < b → b < n+1 → F (u a) < F (u b)) ∧
      (∀ a, n ≤ a → F (n-1) < F (u a)) ∧
      ∀ A ∈ smallSourceUniverse n,
        ∃ color : FullEnvelopeColour N,
          ∀ e : A.Code G, A.FixesPrefix G e →
            fullEnvelopeColour K F N A
              (e.postcompose u hu) = color := by
  obtain ⟨u, hu, hfix, havoid, hcol⟩ :=
    actualFiniteAuxRamsey_completeStage G n K F hF (F (n-1)) N
  refine ⟨u, hu, hfix, ?_, havoid, hcol⟩
  intro a b hab hb
  by_cases hbn : b < n
  · have ha : a < n := lt_trans hab hbn
    simpa only [hfix a ha, hfix b hbn] using
      hprefix a b hab hbn
  · have hbEq : b = n := by omega
    have ha : a < n := by omega
    have hbound : F a ≤ F (n-1) := by
      by_cases heq : a = n-1
      · rw [heq]
      · have halt : a < n-1 := by omega
        exact Nat.le_of_lt
          (hprefix a (n-1) halt (by omega))
    have htail : F (n-1) < F (u n) :=
      havoid n (le_refl n)
    rw [hbEq, hfix a ha]
    exact lt_of_le_of_lt hbound htail

end ATRFiniteDecoder
end ThreeUniformDiaries
