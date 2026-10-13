import ThreeUniformDiaries.FiniteAuxEmbeddingImage
import ThreeUniformDiaries.CountableAembRelativeBranch

/-!
# The finite Aemb converse for genuinely finite embedding colours

An ATR colouring is on m REAL source vertices, represented by
FiniteAuxEmbeddingImage, rather than on full Nat embeddings of the
zero-extension of A.

For every such finite aux embedding with its initial n actual
vertices fixed, choose a certified strictly increasing extension
which satisfies precisely the finite bounded aux-type conditions.
Apply the checked countable finite Aemb converse to this extension,
and identify its literal F_I(g_A(i)) code with the ORIGINAL finite
image at each i<m. The arbitrary extension tail is immaterial.

This is the missing bridge from arbitrary finite-colouring inputs
to genuine finite synchronized E0/E1/E2 strong pictures.
-/

namespace ThreeUniformDiaries
namespace EnumNode

/-- The finite Aemb lemma holds for every actual finite aux-type
embedding image into the enumerated target G, not only for globally
aux-preserving embeddings of the source's infinite zero-extension.

The output codes every one of the m actual source branch vertices
by its original finite image; the extension beyond m has no
appearance in the target branch identity. -/
theorem exists_finiteImage_relativeBranch_coding
    {m n : Nat} (A : EnumNode m)
    (G : Ordered3Graph Nat)
    (I : EnumNode n) (hI : G.initialSegment n = I)
    (hm : 0 < m) (hnm : n ≤ m)
    (e : Ordered3Graph.FiniteAuxEmbeddingImage
      A.toOrdered3Graph G m)
    (hfix : ∀ i : Fin m, i.val < n → e.image i = i.val) :
    ∃ (f : Nat → Nat),
      Ordered3Graph.FiniteAuxEmbedding
        A.toOrdered3Graph G f m ∧
      (∀ i : Fin m, f i.val = e.image i) ∧
      ∃ N : Nat, f (m - 1) < N ∧
      ∃ (r₀ : EnumNode (f 0))
        (r₁ : OneNode (f 0))
        (r₂ : AuxNode (f 0)),
      ∃ (S₀ S₁ S₂ : Set CoordNode),
      ∃ (h₀ : CoordNode.FiniteStrongPicture
          S₀ f (m - 1) (.enum (f 0) r₀))
        (h₁ : CoordNode.FiniteStrongPicture
          S₁ f (m - 1) (.one (f 0) r₁))
        (h₂ : CoordNode.FiniteStrongPicture
          S₂ f (m - 1) (.aux (f 0) r₂)),
      ∀ i : Fin m,
        (⟨f i.val,
          (CoordNode.finiteStrongPicture_enumCanonicalMap
            h₀ h₁ h₂ i.val (by omega) (A.truncate i.val)).val.succ
          (CoordNode.finiteStrongPicture_oneCanonicalMap
            h₁ h₂ i.val (by omega)
            (A.oneType i.val i.val)).val⟩ :
          EnumerationBranchNode) =
          (G.relativeBranchNode I hI (e.image i)).val := by
  obtain ⟨f, hf, he⟩ := e.admissible
  have hfixf : ∀ j : Nat, j < n → f j = j := by
    intro j hj
    have hjm : j < m := by omega
    exact (he ⟨j, hjm⟩).symm.trans (hfix ⟨j, hjm⟩ hj)
  obtain ⟨N, hN, r₀, r₁, r₂, S₀, S₁, S₂,
      h₀, h₁, h₂, hCode⟩ :=
    A.exists_countableAemb_relativeBranch_coding
      G I hI f hf hnm hm hfixf
  refine ⟨f, hf, (fun i => (he i).symm),
    N, hN, r₀, r₁, r₂, S₀, S₁, S₂,
    h₀, h₁, h₂, ?_⟩
  intro i
  calc
    (⟨f i.val,
      (CoordNode.finiteStrongPicture_enumCanonicalMap
        h₀ h₁ h₂ i.val (by omega) (A.truncate i.val)).val.succ
      (CoordNode.finiteStrongPicture_oneCanonicalMap
        h₁ h₂ i.val (by omega) (A.oneType i.val i.val)).val⟩ :
      EnumerationBranchNode) =
        (G.relativeBranchNode I hI (f i.val)).val :=
          hCode i.val i.isLt
    _ = (G.relativeBranchNode I hI (e.image i)).val := by
      rw [he i]

end EnumNode
end ThreeUniformDiaries
