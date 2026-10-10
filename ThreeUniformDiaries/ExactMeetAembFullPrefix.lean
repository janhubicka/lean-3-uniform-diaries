import ThreeUniformDiaries.ExactMeetAembRelativeBranchMap
import ThreeUniformDiaries.FiniteAembCompletePrefix
import ThreeUniformDiaries.FiniteTargetReduction

/-!
# The full geometric finite converse: complete prefix and exact branches

Lemma Aemb needs not only a finite strong vector picture and equality
of its canonical branch map on the actual source copy, but also the
complete fixed initial n levels of every coordinate tree.

The typed finite coding theorem retains E0, E1 and E2^- literally.
Hence the finite completion has ALL nodes at every ambient level j<n
in all three coordinates, and the derived exact-meet branch equality
holds simultaneously. This proves the Str_{n,m} fixed-prefix
requirement under the original capped meet conditions.

The remaining global canonical-map interface is extending the finite
branchMap from K_empty to the relative K_I carrier on *all* its
vertices, beyond the selected source branch. Vector Milliken and
infinite canonical composition are separately tracked.
-/

namespace ThreeUniformDiaries
namespace EnumNode

theorem exists_exactMeetAemb_fullPrefix_branchMap
    {m n : Nat} (A : EnumNode m) (G : Ordered3Graph Nat)
    (I : EnumNode n)
    (hA : A.toOrdered3Graph.initialSegment n = I)
    (hG : G.initialSegment n = I)
    (f : Nat → Nat)
    (hf : Ordered3Graph.FiniteExactMeetEmbedding
      A.toOrdered3Graph G f m)
    (hnm : n ≤ m) (hm : 0 < m)
    (hfix : ∀ j < n, f j = j) :
    ∃ (r₀ : EnumNode (f 0)) (r₁ : OneNode (f 0))
      (r₂ : AuxNode (f 0)),
      ∃ (S₀ S₁ S₂ : Set CoordNode),
      ∃ (h₀ : CoordNode.FiniteStrongPicture S₀ f (m - 1)
        (.enum (f 0) r₀))
        (h₁ : CoordNode.FiniteStrongPicture S₁ f (m - 1)
          (.one (f 0) r₁))
        (h₂ : CoordNode.FiniteStrongPicture S₂ f (m - 1)
          (.aux (f 0) r₂)),
      (∀ (j : Nat) (hj : j < n) (B : EnumNode j),
        CoordNode.enum j B ∈ S₀) ∧
      (∀ (j : Nat) (hj : j < n) (B : OneNode j),
        CoordNode.one j B ∈ S₁) ∧
      (∀ (j : Nat) (hj : j < n) (B : AuxNode j),
        CoordNode.aux j B ∈ S₂) ∧
      (∀ (i : Nat) (him : i < m),
        CoordNode.finiteStrongPicture_branchMap h₀ h₁ h₂
          (A.toOrdered3Graph.relativeBranchNode I hA i).val
          (by change i ≤ m - 1; omega) =
          (G.relativeBranchNode I hG (f i)).val) := by
  let N := f (m - 1) + 1
  have hN : f (m - 1) < N := Nat.lt_succ_self _
  have hfinite :
      Ordered3Graph.FiniteAuxEmbedding A.toOrdered3Graph
        (G.initialSegment N).toOrdered3Graph f m :=
    Ordered3Graph.FiniteAuxEmbedding.target_initialSegment
      A G f hf.toFiniteAuxEmbedding hm N hN
  obtain ⟨r₀, r₁, r₂, S₀, S₁, S₂,
      h₀, h₁, h₂, hinc₀, hinc₁, hinc₂, hCodes⟩ :=
    A.exists_finiteAemb_coding_of_finite
      (G.initialSegment N) f hfinite n hnm hm hfix
  have hprefix :=
    threeCandidate_fullPrefix
      A (G.initialSegment N) f n hinc₀ hinc₁ hinc₂
  rcases hprefix with ⟨hpre₀, hpre₁, hpre₂⟩
  refine ⟨r₀, r₁, r₂, S₀, S₁, S₂,
    h₀, h₁, h₂, hpre₀, hpre₁, hpre₂, ?_⟩
  intro i him
  have hi : i ≤ m - 1 := by omega
  have hfi : f i ≤ f (m - 1) := hf.strictMono.monotone hi
  have hcut : f i + 1 ≤ N := by dsimp [N]; omega
  have hCode : 
      (CoordNode.finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ i
        (by omega) (A.truncate i)).val.succ
        (CoordNode.finiteStrongPicture_oneCanonicalMap h₁ h₂ i
          (by omega) (A.oneType i i)).val =
        G.initialSegment (f i + 1) := by
    simpa [G.initialSegment_truncate hcut] using hCodes i him
  change CoordNode.finiteStrongPicture_branchMap h₀ h₁ h₂
      (A.toOrdered3Graph.branchNode i)
      (by change i ≤ m - 1; omega) =
      (G.relativeBranchNode I hG (f i)).val
  calc
    CoordNode.finiteStrongPicture_branchMap h₀ h₁ h₂
        (A.toOrdered3Graph.branchNode i)
        (by change i ≤ m - 1; omega) =
      (⟨f i,
        (CoordNode.finiteStrongPicture_enumCanonicalMap
          h₀ h₁ h₂ i (by omega) (A.truncate i)).val.succ
        (CoordNode.finiteStrongPicture_oneCanonicalMap
          h₁ h₂ i (by omega) (A.oneType i i)).val⟩ :
          EnumerationBranchNode) :=
      CoordNode.finiteStrongPicture_branchMap_source
        A h₀ h₁ h₂ i (by omega)
    _ = (G.relativeBranchNode I hG (f i)).val :=
      A.finiteCanonical_code_eq_relativeBranchNode
        G I hG h₀ h₁ h₂ i (by omega) hCode

end EnumNode
end ThreeUniformDiaries
