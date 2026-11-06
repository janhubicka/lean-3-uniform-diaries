import ThreeUniformDiaries.DiaryFiniteCandidatePersistentFusion
import ThreeUniformDiaries.DiaryGenericExistenceByPairCode

/-!
# Persistent finite covers produce an ACTUAL certified fusion system

Track D's checked theorem
  exists_fullDiaryEmbedding_of_persistent_finite_covers
already constructs a CertifiedDiaryFusionData object internally
and immediately extracts its infinite embedding. This module
exports that intermediate Type-valued certificate directly.

The Safe predicate is NONCIRCULAR: PersistentReservedDiaryStage
means an actual reserved finite stage with extensions at EVERY
separately prescribed finite horizon preserving the old support.
If, at every such persistent genuine-leaf stage, one FINITE set
of possible next target leaf images covers all finite horizons,
the checked finite-choice theorem produces a persistent successor.
Nonleaf stages extend without changing the support. The verified
independent finite reserved-stage existence theorem gives the
marker-only base.

Unlike the historical statement, the generic G is not an input:
we use the explicitly constructed canonicalGenericEnumerated3Graph.

This definition DOES NOT prove the finite-next-image cover
hypothesis or countable diary unavoidability. All its data come
from previously verified finite predicates.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

/-- The actual certified Safe-stage fusion structure, assembled from
a role-diary source H, a role-diary target K, a countably universal
U with prescribed unordered induced leaf map F:U→K, and independent
FINITE next-image covers for all finitely persistent source leaf stages.

There is no generic-structure or existence-of-infinite-embedding
assumption. Crucially, the finite-cover hypothesis is an explicit
input, not silently derived from separate finite-horizon copies. -/
noncomputable def certifiedFusion_of_persistent_finite_covers
    {H U K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (hUniversal : CountablyUniversal U)
    (F : UnorderedEmbedding U K)
    (hFleaf : ∀ t : Nat, IsLeaf K (F t))
    (hFiniteCover : ∀ m : Nat, IsLeaf H m →
      ∀ f : Nat → Nat,
        PersistentReservedDiaryStage H K (fun t => F t) m f →
        FiniteHorizonNextLeafCover H K (fun t => F t) m f) :
    CertifiedDiaryFusionData DH K (fun t => F t) := by
  classical
  exact {
    Safe := PersistentReservedDiaryStage H K (fun t => F t)
    valid := by
      intro m f P
      exact P.1.1
    initial := by
      exact ⟨fun u => u,
        persistent_reserved_marker_base
          DH DK canonicalGenericEnumerated3Graph
          hUniversal F hFleaf⟩
    next := by
      intro m f P
      by_cases hm : IsLeaf H m
      · obtain ⟨g, hPersistent, hCompatible⟩ :=
          exists_persistent_reserved_successor_of_finite_cover
            hm (hFiniteCover m hm f P)
        exact ⟨g, hPersistent, hCompatible⟩
      · exact ⟨f, P.extend_of_not_leaf hm, by intro u hu; rfl⟩
  }

/-- In particular a finite-cover hypothesis provides an inhabited
Type-valued certificate, which can be supplied to the checked
COFINAL Safe-fusion Track A upper interface. -/
theorem nonempty_certifiedFusion_of_persistent_finite_covers
    {H U K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (hUniversal : CountablyUniversal U)
    (F : UnorderedEmbedding U K)
    (hFleaf : ∀ t : Nat, IsLeaf K (F t))
    (hFiniteCover : ∀ m : Nat, IsLeaf H m →
      ∀ f : Nat → Nat,
        PersistentReservedDiaryStage H K (fun t => F t) m f →
        FiniteHorizonNextLeafCover H K (fun t => F t) m f) :
    Nonempty (CertifiedDiaryFusionData DH K (fun t => F t)) :=
  ⟨certifiedFusion_of_persistent_finite_covers
    DH DK hUniversal F hFleaf hFiniteCover⟩

end DiaryLeafPriority
end ThreeUniformDiaries
