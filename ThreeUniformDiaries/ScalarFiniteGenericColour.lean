import ThreeUniformDiaries.FiniteStrongGenericPhiCode
import ThreeUniformDiaries.ScalarProtectedRelativeDecode

/-!
# The actual finite scalar Milliken colour is an ATR embedding in G

For a finite scalar approximation of the real root-glued type tree,
with the first n+1 scalar levels protected, its intrinsic finite
decoder has genuine E0/E1/E2 strong-coordinate pictures on the
canonical realization-independent selected height map.

Their finite F_I action on g_A is a genuine aux-type-respecting
induced embedding into G, using the one fixed uniform K_I embedding
chosen before colouring. Moreover its value on EVERY source vertex
is literally phi(index_I(F_I^a(g_A(i)))).

This closes the finite-colour well-definedness step in the actual
scalar Milliken application. The heterogeneous Milliken input and
the subsequent realization/monochromaticity argument are separate.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Milliken
open Milliken.GeneralTree
open ThreeUniformDiaries.CoordNode

/-- Each identity-stem-protected scalar finite approximation produces
an actual aux-type-respecting embedding into G, with the exact finite
F_I formula evaluated on the intrinsic scalar decoder and the fixed
universal phi. There is no colouring of artificial branch tuples. -/
theorem exists_scalarFinite_phi_FI_gA_auxEmbedding
    (G : GenericEnumerated3Graph)
    {k n : Nat} (hnk : n ≤ k + 1)
    (A : EnumNode (k + 1))
    (I : EnumNode n) (hI : A.truncate n = I)
    (E : SizeFirstBranchPresentation I)
    (phi : Nat → Nat)
    (hphi : UniversalAuxBranchProperty G I E phi)
    (a : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2))
    (hvalid : ∃ S : StrongSubtree CoordNode.rootGluedAmbientTree,
      r (k + 2) S = a ∧
      r (n + 1) S = r (n + 1) scalarIdentity) :
    ∃ e : Ordered3Graph.Embedding A.toOrdered3Graph G.graph,
      e.AuxTypeRespecting ∧
      (∀ j : Nat, j < n → e j = j) ∧
      ∀ i : Fin (k + 1),
        ∃ hB : InRelativeBranchGraph I
          (rootedScalarFiniteBranchMap k a
            (protectedScalarApprox_root_mem k n a hvalid)
            (A.toOrdered3Graph.branchNode i.val)
            (Nat.le_of_lt_succ i.isLt)),
          e i.val =
            phi (E.code.symm
              (⟨rootedScalarFiniteBranchMap k a
                  (protectedScalarApprox_root_mem k n a hvalid)
                  (A.toOrdered3Graph.branchNode i.val)
                  (Nat.le_of_lt_succ i.isLt), hB⟩ :
                RelativeBranchNode I)) := by
  obtain ⟨S, hSa, hstem⟩ := hvalid
  have hS : a.carrier = S.initialPart (k + 2) :=
    congrArg FiniteApprox.carrier hSa.symm
  have hroot : (none : WithBot CoordNode) ∈ a.carrier :=
    protectedScalarApprox_root_mem k n a ⟨S, hSa, hstem⟩
  let g := canonicalFiniteLevelMap k a
  obtain ⟨r₀, r₁, r₂, h₀, h₁, h₂⟩ :=
    finiteCode_has_canonical_pictures k a hroot
  have hg : StrictMono g := canonicalFiniteLevelMap_strictMono k a
  have hfix : ∀ j < n, g j = j := by
    intro j hj
    have hjk : j ≤ k := by omega
    have hSfix := (anchoredScalar_root_and_levels S n hstem).2 j hj
    exact (canonicalFiniteLevelMap_eq_realizer k a S hS j hjk).trans hSfix
  obtain ⟨e, he, hefix, hphiCode⟩ :=
    exists_finiteStrong_phi_FI_gA_auxEmbedding
      G I E phi hphi h₀ h₁ h₂ hg A hI hfix
  refine ⟨e, he, hefix, ?_⟩
  intro i
  obtain ⟨hB, hvalue⟩ := hphiCode i
  have hcode :=
    rootedScalarFiniteBranchMap_eq_of_pictures
      k a hroot h₀ h₁ h₂
      (A.toOrdered3Graph.branchNode i.val)
      (Nat.le_of_lt_succ i.isLt)
  have hroot_eq :
      (protectedScalarApprox_root_mem k n a ⟨S, hSa, hstem⟩) =
        hroot := Subsingleton.elim _ _
  have hB' : InRelativeBranchGraph I
      (rootedScalarFiniteBranchMap k a
        (protectedScalarApprox_root_mem k n a ⟨S, hSa, hstem⟩)
        (A.toOrdered3Graph.branchNode i.val)
        (Nat.le_of_lt_succ i.isLt)) := by
    rw [hroot_eq, hcode]
    exact hB
  refine ⟨hB', ?_⟩
  simpa only [hroot_eq, hcode] using hvalue

end ATRFiniteDecoder
end ThreeUniformDiaries
