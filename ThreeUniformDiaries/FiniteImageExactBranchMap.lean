import ThreeUniformDiaries.FiniteImageAembCoding
import ThreeUniformDiaries.FiniteCanonicalBranchMap

/-!
# Full finite Aemb converse in the literal F_I branch-map API

The earlier genuinely finite Aemb theorem gives the correct
E0/E1/E2 coordinate images, but states its conclusion as the expanded
last-vertex successor formula. The scalar Ramsey realisation theorem
uses the *whole* `finiteStrongPicture_branchMap` function on universal
branch vertices.

We identify these terms exactly, on every source vertex of A, keeping
the finite-image colour domain and not imposing any type constraints
on the infinitely zero-extended source above |A|. This closes the
last representation mismatch between the finite embedding converse
and the protected geometric scalar refinement.
-/

namespace ThreeUniformDiaries
namespace EnumNode

/-- Every genuine finite aux-type embedding gives finite synchronized
strong E0/E1/E2 pictures whose COMPLETE canonical F_I branch values
on the m actual source vertices are exactly g_G(e(i)). -/
theorem exists_finiteImage_exact_branchMap
    {m n : Nat}
    (A : EnumNode m)
    (G : Ordered3Graph Nat)
    (I : EnumNode n) (hI : G.initialSegment n = I)
    (hm : 0 < m) (hnm : n ≤ m)
    (e : Ordered3Graph.FiniteAuxEmbeddingImage
      A.toOrdered3Graph G m)
    (hfix : ∀ i : Fin m, i.val < n → e.image i = i.val) :
    ∃ (f : Nat → Nat),
      StrictMono f ∧
      (∀ j < n, f j = j) ∧
      ∃ (r₀ : EnumNode (f 0))
        (r₁ : OneNode (f 0))
        (r₂ : AuxNode (f 0)),
      ∃ (S₀ S₁ S₂ : Set CoordNode),
      ∃ (h₀ : CoordNode.FiniteStrongPicture S₀ f (m - 1)
            (.enum (f 0) r₀))
        (h₁ : CoordNode.FiniteStrongPicture S₁ f (m - 1)
            (.one (f 0) r₁))
        (h₂ : CoordNode.FiniteStrongPicture S₂ f (m - 1)
            (.aux (f 0) r₂)),
      ∀ i : Fin m,
        CoordNode.finiteStrongPicture_branchMap h₀ h₁ h₂
          (A.toOrdered3Graph.branchNode i.val)
          (by omega : i.val ≤ m - 1) =
        G.branchNode (e.image i) := by
  obtain ⟨f, hfin, himage, N, hN, r₀, r₁, r₂,
      S₀, S₁, S₂, h₀, h₁, h₂, hcode⟩ :=
    A.exists_finiteImage_relativeBranch_coding
      G I hI hm hnm e hfix
  have hf : StrictMono f := hfin.strictMono
  have hfixF : ∀ j < n, f j = j := by
    intro j hj
    have hjm : j < m := by omega
    calc
      f j = e.image ⟨j, hjm⟩ := himage ⟨j, hjm⟩
      _ = j := hfix ⟨j, hjm⟩ hj
  refine ⟨f, hf, hfixF,
    r₀, r₁, r₂, S₀, S₁, S₂, h₀, h₁, h₂, ?_⟩
  intro i
  have hi : i.val ≤ m - 1 := by omega
  have hsource :=
    CoordNode.finiteStrongPicture_branchMap_source
      A h₀ h₁ h₂ i.val hi
  have hvalue := hcode i
  change
    (⟨f i.val,
      (CoordNode.finiteStrongPicture_enumCanonicalMap
        h₀ h₁ h₂ i.val (by omega) (A.truncate i.val)).val.succ
      (CoordNode.finiteStrongPicture_oneCanonicalMap
        h₁ h₂ i.val (by omega) (A.oneType i.val i.val)).val⟩ :
        EnumerationBranchNode) =
      G.branchNode (e.image i) at hvalue
  exact hsource.trans hvalue

end EnumNode
end ThreeUniformDiaries
