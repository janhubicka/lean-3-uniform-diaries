import ThreeUniformDiaries.CountableAembCanonicalCoding
import ThreeUniformDiaries.RelativeBranchHypergraph

/-!
# The Aemb canonical code as an actual vertex of the manuscript's K_I

The explicit finite canonical code of a source branch vertex i is
an EnumNode of length f(i)+1. Pairing it with last index f(i)
produces an EnumerationBranchNode of K_empty. The countable target
coding theorem proves it literally equals G.branchNode(f(i)), hence
also the underlying vertex of g_G(f(i)) in relative K_I whenever
I=G|n.

This is a representation-level identity for the *actual branch
vertices*, not a claim that the abstract CanonicalMap structure has
been instantiated on all of K_I. It closes the finite converse's
relative-branch equality on g_A[A].
-/

namespace ThreeUniformDiaries
namespace EnumNode

theorem finiteCanonical_code_eq_relativeBranchNode
    {m N : Nat} (A : EnumNode m) (G : Ordered3Graph Nat)
    {n : Nat} (I : EnumNode n)
    (hI : G.initialSegment n = I)
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {k : Nat}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : CoordNode.FiniteStrongPicture S₀ f k
      (.enum (f 0) r₀))
    (h₁ : CoordNode.FiniteStrongPicture S₁ f k
      (.one (f 0) r₁))
    (h₂ : CoordNode.FiniteStrongPicture S₂ f k
      (.aux (f 0) r₂))
    (i : Nat) (hi : i ≤ k)
    (hCode :
      (CoordNode.finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ i hi
        (A.truncate i)).val.succ
        (CoordNode.finiteStrongPicture_oneCanonicalMap h₁ h₂ i hi
          (A.oneType i i)).val =
        G.initialSegment (f i + 1)) :
    (⟨f i,
      (CoordNode.finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ i hi
        (A.truncate i)).val.succ
        (CoordNode.finiteStrongPicture_oneCanonicalMap h₁ h₂ i hi
          (A.oneType i i)).val⟩ : EnumerationBranchNode) =
      (G.relativeBranchNode I hI (f i)).val := by
  change (⟨f i,
      (CoordNode.finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ i hi
        (A.truncate i)).val.succ
        (CoordNode.finiteStrongPicture_oneCanonicalMap h₁ h₂ i hi
          (A.oneType i i)).val⟩ : EnumerationBranchNode) =
      G.branchNode (f i)
  exact congrArg
    (fun B : EnumNode (f i + 1) =>
      (⟨f i, B⟩ : EnumerationBranchNode)) hCode

theorem exists_countableAemb_relativeBranch_coding
    {m n : Nat} (A : EnumNode m) (G : Ordered3Graph Nat)
    (I : EnumNode n) (hI : G.initialSegment n = I)
    (f : Nat → Nat)
    (hf : Ordered3Graph.FiniteAuxEmbedding
      A.toOrdered3Graph G f m)
    (hnm : n ≤ m) (hm : 0 < m)
    (hfix : ∀ j < n, f j = j) :
    ∃ N : Nat, f (m - 1) < N ∧
      ∃ (r₀ : EnumNode (f 0)) (r₁ : OneNode (f 0))
        (r₂ : AuxNode (f 0)),
      ∃ (S₀ S₁ S₂ : Set CoordNode),
      ∃ (h₀ : CoordNode.FiniteStrongPicture S₀ f (m - 1)
        (.enum (f 0) r₀))
        (h₁ : CoordNode.FiniteStrongPicture S₁ f (m - 1)
          (.one (f 0) r₁))
        (h₂ : CoordNode.FiniteStrongPicture S₂ f (m - 1)
          (.aux (f 0) r₂)),
      ∀ (i : Nat) (him : i < m),
        (⟨f i,
          (CoordNode.finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ i
            (by omega) (A.truncate i)).val.succ
          (CoordNode.finiteStrongPicture_oneCanonicalMap h₁ h₂ i
            (by omega) (A.oneType i i)).val⟩ :
          EnumerationBranchNode) =
            (G.relativeBranchNode I hI (f i)).val := by
  obtain ⟨N, hN, r₀, r₁, r₂, S₀, S₁, S₂,
      h₀, h₁, h₂, hCode⟩ :=
    A.exists_countableAemb_coding G f hf n hnm hm hfix
  refine ⟨N, hN, r₀, r₁, r₂, S₀, S₁, S₂,
    h₀, h₁, h₂, ?_⟩
  intro i him
  exact A.finiteCanonical_code_eq_relativeBranchNode
    G I hI h₀ h₁ h₂ i (by omega) (hCode i him)

end EnumNode
end ThreeUniformDiaries
