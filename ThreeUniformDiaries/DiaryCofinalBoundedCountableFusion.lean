import ThreeUniformDiaries.DiaryFiniteCandidatePersistentFusion
import ThreeUniformDiaries.DiaryGenericExistenceByPairCode

/-!
# Countable diary fusion from a cofinal numerical new-leaf bound

Previous theorems show that finite-horizon persistent reserved stages
fuse into an ACTUAL countable full diary embedding provided each
persistent genuine leaf stage has a finite set of possible next-leaf
images covering every future finite horizon.

It is enough to ask for ONE numerical bound B attained along
ARBITRARILY LARGE horizons. A horizon witness at n >= N restricts
to horizon N without changing any images or old-support compatibility.
Thus a uniform bound at cofinally many horizons gives the required
finite leaf image cover at every horizon.

This theorem eliminates the external generic-G parameter by
using the verified explicit pair-coded enumerated generic graph.
It does NOT construct B, prove tail-richness, or establish the
unconditional countable diary-unavoidability theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A fixed old reserved stage admits bounded next-leaf
realizations through ARBITRARILY HIGH finite horizons. The bound
depends on the old stage but NOT on the horizon; no split-profile
selection or coherent infinite family is postulated. -/
def HasCofinalBoundedNextLeafImages
    (H K : Ordered3Graph Nat) (F f : Nat → Nat) (m : Nat) :
    Prop :=
  ∃ B : Nat, ∀ N : Nat, ∃ n : Nat, N ≤ n ∧
    ∃ g : Nat → Nat,
      ReservedDiaryStage H K F (m + 1 + n) g ∧
      CofinalDiaryStageCompatible H m f g ∧
      g m ≤ B

/-- Cofinal bounded horizon witnesses give a genuine FINITE
next-leaf image cover at ALL horizons by literal stage restriction. -/
theorem finiteHorizonNextLeafCover_of_cofinal_bounded_images
    (H K : Ordered3Graph Nat) (F f : Nat → Nat) (m : Nat)
    (hCofinal : HasCofinalBoundedNextLeafImages H K F f m) :
    FiniteHorizonNextLeafCover H K F m f := by
  classical
  obtain ⟨B, hAll⟩ := hCofinal
  refine ⟨Finset.range (B + 1), ?_⟩
  intro N
  obtain ⟨n, hNn, g, Q, hOld, hBound⟩ := hAll N
  have QN : ReservedDiaryStage H K F (m + 1 + N) g :=
    Q.restrict (by omega)
  exact ⟨g, QN, hOld, Finset.mem_range.mpr (by omega)⟩

/-- An ACTUAL countable full source diary H embeds into a full
target diary K with all genuine leaves in the prescribed range
F[U], preserving induced triples/nontriples and both numerical
leaf meets, if every persistent genuine leaf stage has a uniform
next-image bound realized at cofinally high finite horizons.

No supplied generic enumerated hypergraph, finite-cover family,
Safe predicate, countable coherent mapping, or arbitrary relative
new-leaf extension hypothesis is required. The numerical-bound
condition is a genuine extra geometric hypothesis. -/
theorem exists_fullDiaryEmbedding_of_cofinal_bounded_leaf_images
    {H U K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (hUniversal : Ordered3Graph.CountablyUniversal U)
    (F : Ordered3Graph.UnorderedEmbedding U K)
    (hFleaf : ∀ t : Nat, IsLeaf K (F t))
    (hBound : ∀ m : Nat, IsLeaf H m →
      ∀ f : Nat → Nat,
        PersistentReservedDiaryStage H K F m f →
        HasCofinalBoundedNextLeafImages H K F f m) :
    ∃ e : Ordered3Graph.Embedding H K,
      (∀ u : Nat, IsLeaf H u → ∃ t : Nat, e u = F t) ∧
      (∀ u v : Nat, 3 ≤ u → 3 ≤ v →
        K.oneMeetLevel (e u) (e v) =
          e (H.oneMeetLevel u v)) ∧
      (∀ a b c d : Nat, a < b → c < d →
        3 ≤ a → 3 ≤ c →
        K.twoMeetLevel (e a) (e b) (e c) (e d) =
          e (H.twoMeetLevel a b c d)) := by
  exact exists_fullDiaryEmbedding_of_persistent_finite_covers
    DH DK canonicalGenericEnumerated3Graph hUniversal F hFleaf
    (by
      intro m hm f P
      exact finiteHorizonNextLeafCover_of_cofinal_bounded_images
        H K F f m (hBound m hm f P))

/-- A cofinal bound on CHOSEN INDICES of the prescribed leaf range
is likewise sufficient. The outer leaf embedding F need not
preserve numerical order: the finite image of range B has a
uniform maximum in the target order. -/
theorem exists_fullDiaryEmbedding_of_cofinal_bounded_leaf_indices
    {H U K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (hUniversal : Ordered3Graph.CountablyUniversal U)
    (F : Ordered3Graph.UnorderedEmbedding U K)
    (hFleaf : ∀ t : Nat, IsLeaf K (F t))
    (hIndex : ∀ m : Nat, IsLeaf H m →
      ∀ f : Nat → Nat,
        PersistentReservedDiaryStage H K F m f →
        ∃ B : Nat, ∀ N : Nat, ∃ n : Nat, N ≤ n ∧
          ∃ g : Nat → Nat,
            ReservedDiaryStage H K F (m + 1 + n) g ∧
            CofinalDiaryStageCompatible H m f g ∧
            ∃ t : Nat, t < B ∧ g m = F t) :
    ∃ e : Ordered3Graph.Embedding H K,
      (∀ u : Nat, IsLeaf H u → ∃ t : Nat, e u = F t) ∧
      (∀ u v : Nat, 3 ≤ u → 3 ≤ v →
        K.oneMeetLevel (e u) (e v) =
          e (H.oneMeetLevel u v)) ∧
      (∀ a b c d : Nat, a < b → c < d →
        3 ≤ a → 3 ≤ c →
        K.twoMeetLevel (e a) (e b) (e c) (e d) =
          e (H.twoMeetLevel a b c d)) := by
  apply exists_fullDiaryEmbedding_of_cofinal_bounded_leaf_images
    DH DK hUniversal F hFleaf
  intro m hm f P
  obtain ⟨B, hAll⟩ := hIndex m hm f P
  refine ⟨(Finset.range B).sup F, ?_⟩
  intro N
  obtain ⟨n, hNn, g, Q, hOld, t, ht, hEq⟩ := hAll N
  refine ⟨n, hNn, g, Q, hOld, ?_⟩
  rw [hEq]
  exact Finset.le_sup (f := F) (Finset.mem_range.mpr ht)

end DiaryLeafPriority
end ThreeUniformDiaries
