import ThreeUniformDiaries.DiaryFiniteSingletonTypeCover
import ThreeUniformDiaries.DiarySingletonAvoidanceFamily

/-!
# Uniform finite avoidance across ALL generic singleton types

The generic 3-hypergraph has only finitely many singleton edge masks
below a fixed cut n. Choose a representative vertex for each mask,
and take its native n+1-vertex singleton envelope. This yields a
finite list of genuine singleton ATR sources.

The simultaneous finite-family avoidance theorem produces a SINGLE
prefix-fixing aux-type-respecting generic self-embedding avoiding a
given finite outer-image interval for every source in the list.

Every other vertex a >= n has exactly the same finite EnumNode
source as one of these representatives. Transport the canonical
finite embedding code of a to the representative source using that
equality. The finite-family avoidance conclusion then applies to a.

This closes the finite-avoidance assertion at one protected cut,
without assuming the arbitrary injective outer map is increasing
and without colouring any artificial infinite source tail.
-/

namespace ThreeUniformDiaries
namespace GenericEnumerated3Graph

open Ordered3Graph
open ATRFiniteDecoder

/-- A representative singleton envelope realising one Boolean
edge mask below the protected cut. -/
noncomputable def singletonShapeForMask
    (G : GenericEnumerated3Graph) (n : Nat)
    (p : Fin n → Fin n → Bool) :
    SingletonShape G n :=
  { terminal := G.singletonRepresentative n p
    envelope :=
      FiniteSingletonEnvelope.ofVertex G.graph n
        (G.singletonRepresentative n p)
        (G.singletonRepresentative_spec n p).1 }

/-- Finite family containing representatives of every singleton
type and every native finite singleton-envelope source at cut n. -/
noncomputable def allSingletonShapes
    (G : GenericEnumerated3Graph) (n : Nat) :
    List (SingletonShape G n) := by
  classical
  exact (Finset.univ : Finset (Fin n → Fin n → Bool)).toList.map
    (fun p => G.singletonShapeForMask n p)

theorem singletonShapeForMask_mem
    (G : GenericEnumerated3Graph) (n : Nat)
    (p : Fin n → Fin n → Bool) :
    G.singletonShapeForMask n p ∈ G.allSingletonShapes n := by
  classical
  unfold allSingletonShapes
  exact List.mem_map.mpr ⟨p, by simp, rfl⟩

/-- Complete one-cut forbidden-colour elimination. For any injective
outer F and any M, one generic aux-type-respecting self-embedding
u fixes the protected prefix n and sends EVERY vertex a>=n
past M under F∘u. The proof works uniformly across all singleton
types through the finite list of representative sources. -/
theorem exists_prefix_fixed_avoiding_refinement
    (G : GenericEnumerated3Graph)
    (n : Nat)
    (F : Nat → Nat) (hF : Function.Injective F)
    (M : Nat) :
    ∃ (u : Embedding G.graph G.graph)
      (hu : u.AuxTypeRespecting),
      (∀ t < n, u t = t) ∧
      ∀ a, n ≤ a → M < F (u a) := by
  classical
  obtain ⟨u, hu, hfix, hAvoid⟩ :=
    actualFiniteSingletonATR_avoidFamily
      G n F hF M (G.allSingletonShapes n)
  refine ⟨u, hu, hfix, ?_⟩
  intro a hna
  let p := G.singletonMask n a
  let S : SingletonShape G n := G.singletonShapeForMask n p
  let E : FiniteSingletonEnvelope G.graph n a :=
    FiniteSingletonEnvelope.ofVertex G.graph n a hna
  have hS : S ∈ G.allSingletonShapes n := by
    exact G.singletonShapeForMask_mem n p
  have htype : G.graph.SameOneTypeBelow n a S.terminal := by
    change G.graph.SameOneTypeBelow n a
      (G.singletonRepresentative n (G.singletonMask n a))
    exact G.singletonRepresentative_sameOneType n a
  have hEnum : E.finiteEnum = S.envelope.finiteEnum :=
    E.finiteEnum_eq_of_sameOneType S.envelope htype
  have hf : FiniteAuxEmbedding
      S.envelope.finiteEnum.toOrdered3Graph G.graph
      E.enumerate (n+1) := by
    rw [← hEnum]
    exact E.finite_aux_embedding.of_initialSegment
  let e : FiniteAuxEmbeddingImage
      S.envelope.finiteEnum.toOrdered3Graph G.graph (n+1) :=
    FiniteAuxEmbeddingImage.ofFiniteAuxEmbedding E.enumerate hf
  have hefix : ∀ i : Fin (n+1),
      i.val < n → e.image i = i.val := by
    intro i hi
    change E.enumerate i.val = i.val
    exact E.protected_prefix i.val hi
  have hlast : e.image (Fin.last n) = a := by
    change E.enumerate n = a
    exact E.endpoint
  have h := hAvoid S hS e hefix
  simpa only [hlast] using h

end GenericEnumerated3Graph
end ThreeUniformDiaries
