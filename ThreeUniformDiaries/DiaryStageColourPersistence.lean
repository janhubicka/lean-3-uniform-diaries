import ThreeUniformDiaries.DiaryOrderedStageRecursion

/-!
# Persistence of all finite type/orientation colours through the stage recursion

A complete finite ATR stage at source cut i fixes the prefix i and
makes the complete singleton/pair/orientation colour constant on
all finite embeddings of every small native source shape at that
cut. Every later stage is a further prefix-fixing aux-type-
respecting refinement, so each earlier colour stays constant.

The target cut at i is the predecessor outer image plus one:
    N_i = F(g(i-1)) + 1.
The refinement at stage i fixes i-1; therefore N_i is literally
unchanged at every later stage. This file proves the persistent
colour invariant for the recursively chosen sequence of stages.

Only G's actual finite embedding images are coloured. The statement
does not yet reconstruct individual source singleton and diary
pointed-pair equivalences from equality of their native finite
source codes; that is the next transfer to the manuscript's (I2)
and (I3).
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Ordered3Graph

/-- A complete stage has homogenised all small finite ATR source
shapes at every protected cut already visited. At cut i the target
cut is computed from the CURRENT stage's image of i-1; coherence
guarantees that this value never changes in later stages. -/
def OrderedDiaryStage.ColoursStable
    {G : GenericEnumerated3Graph}
    {K : Ordered3Graph Nat} {F : Nat → Nat} {k : Nat}
    (S : OrderedDiaryStage G K F k) : Prop :=
  ∀ (i : Nat), 0 < i → i ≤ k →
    ∀ (A : ProtectedSource i), A ∈ smallSourceUniverse i →
      ∃ color : FullEnvelopeColour (F (S.map (i-1)) + 1),
        ∀ (e : A.Code G), A.FixesPrefix G e →
          fullEnvelopeColour K F (F (S.map (i-1)) + 1) A
            (e.postcompose S.map S.aux) = color

/-- Postcomposition of a genuine finite embedding code with an
ambient aux-type-respecting embedding is literally equivalent
to precomposing the outer evaluation map in the complete finite
colour. Only the last two finite images are read. -/
theorem fullEnvelopeColour_postcompose
    (K : Ordered3Graph Nat) (F : Nat → Nat) (N : Nat)
    {G : GenericEnumerated3Graph} {i : Nat}
    (A : ProtectedSource i) (e : A.Code G)
    (g : Embedding G.graph G.graph) (hg : g.AuxTypeRespecting) :
    fullEnvelopeColour K F N A (e.postcompose g hg) =
      fullEnvelopeColour K (fun v => F (g v)) N A e := by
  simp only [fullEnvelopeColour,
    FiniteAuxEmbeddingImage.postcompose_apply]

namespace OrderedDiaryStage

variable {G : GenericEnumerated3Graph}
  {K : Ordered3Graph Nat} {F : Nat → Nat} {k : Nat}

/-- A fixed cut's code is still prefix-fixed after any later
refinement fixing a longer prefix. -/
theorem Refinement.preservesCodePrefix
    (S : OrderedDiaryStage G K F k)
    (R : S.Refinement)
    (i : Nat) (hi : i ≤ k+1)
    (A : ProtectedSource i)
    (e : A.Code G) (he : A.FixesPrefix G e) :
    A.FixesPrefix G (e.postcompose R.embedding R.aux) := by
  intro j hj
  rw [FiniteAuxEmbeddingImage.postcompose_apply, he j hj]
  exact R.fixes_prefix j.val (by omega)

/-- Earlier finite homogeneity survives the next refinement and
the previously frozen predecessor target cut remains unchanged. -/
theorem ColoursStable.next
    (S : OrderedDiaryStage G K F k)
    (R : S.Refinement)
    (hstable : S.ColoursStable) :
    (S.next R).ColoursStable := by
  intro i hi hik A hA
  by_cases hOld : i ≤ k
  · obtain ⟨color, hc⟩ := hstable i hi hOld A hA
    have hpred : i-1 < k+1 := by omega
    have hcut : F ((S.next R).map (i-1)) + 1 =
        F (S.map (i-1)) + 1 := by
      change F (S.map (R.embedding (i-1))) + 1 =
        F (S.map (i-1)) + 1
      rw [R.fixes_prefix (i-1) hpred]
    rw [hcut]
    refine ⟨color, ?_⟩
    intro e he
    let e' : A.Code G := e.postcompose R.embedding R.aux
    have he' : A.FixesPrefix G e' :=
      Refinement.preservesCodePrefix S R i (by omega) A e he
    have hEq := hc e' he'
    change fullEnvelopeColour K F (F (S.map (i-1)) + 1) A
        (e.postcompose (S.map.comp R.embedding)
          (S.aux.comp R.aux)) = color
    simpa only [e', FiniteAuxEmbeddingImage.postcompose_comp]
      using hEq
  · have hiEq : i = k+1 := by omega
    subst i
    obtain ⟨color, hc⟩ := R.full_colours A hA
    have hcut : F ((S.next R).map ((k+1)-1)) + 1 =
        F (S.map k) + 1 := by
      have hk : (k+1)-1 = k := by omega
      rw [hk]
      change F (S.map (R.embedding k)) + 1 =
        F (S.map k) + 1
      rw [R.fixes_prefix k (by omega)]
    rw [hcut]
    refine ⟨color, ?_⟩
    intro e he
    change fullEnvelopeColour K F (F (S.map k) + 1) A
      (e.postcompose (S.map.comp R.embedding)
        (S.aux.comp R.aux)) = color
    calc
      fullEnvelopeColour K F (F (S.map k) + 1) A
          (e.postcompose (S.map.comp R.embedding)
            (S.aux.comp R.aux)) =
        fullEnvelopeColour K F (F (S.map k) + 1) A
          ((e.postcompose R.embedding R.aux).postcompose
            S.map S.aux) := by
              rw [FiniteAuxEmbeddingImage.postcompose_comp]
      _ = fullEnvelopeColour K
          (fun v => F (S.map v)) (F (S.map k) + 1) A
          (e.postcompose R.embedding R.aux) :=
            fullEnvelopeColour_postcompose
              K F (F (S.map k)+1) A
              (e.postcompose R.embedding R.aux)
              S.map S.aux
      _ = color := hc e he

end OrderedDiaryStage

/-- The recursively constructed diary stage sequence retains
homogeneity of every singleton and pointed-envelope finite colour
at all earlier source cuts, with the exact predecessor target cuts
used in the lower-bound manuscript. -/
theorem orderedDiaryStages_coloursStable
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : Nat → Nat) (hF : Function.Injective F)
    (k : Nat) :
    (orderedDiaryStages G K F hF k).ColoursStable := by
  induction k with
  | zero =>
      intro i hi hik A hA
      omega
  | succ k ih =>
      rw [orderedDiaryStages_succ]
      exact OrderedDiaryStage.ColoursStable.next
        (orderedDiaryStages G K F hF k)
        ((orderedDiaryStages G K F hF k).chooseRefinement hF) ih

end ATRFiniteDecoder
end ThreeUniformDiaries
