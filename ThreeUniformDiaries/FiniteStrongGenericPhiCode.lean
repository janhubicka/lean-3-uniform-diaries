import ThreeUniformDiaries.FiniteStrongGenericColourWellDefined
import ThreeUniformDiaries.SizeFirstSourceTests

/-!
# The actual finite ATR F_I colour uses the single fixed phi

The finite geometric factorisation through H produces a genuine
aux-type-respecting embedding of A into the generic G. To identify
this embedding with the colour written in the manuscript, one must
show its value on EVERY finite vertex i is the fixed uniform
K_I embedding phi applied to the index of the LITERAL finite
F_I^S(g_A(i)) branch vertex.

This theorem proves that exact pointwise identity. The induced and
aux-type-preserving properties are inherited from the checked
composition proof; the equality uses the genuine length-first
K_I enumeration, not an unnamed abstract branch lift.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- The finite strong picture's genuine aux-type-respecting embedding
into G has precisely the manuscript's vertex map
  i ↦ phi (index_I (F_I^S (g_A(i)))).
The same (E,phi) is fixed once for the generic target and I. -/
theorem exists_finiteStrong_phi_FI_gA_auxEmbedding
    (G : GenericEnumerated3Graph)
    {k n : Nat} (I : EnumNode n)
    (E : SizeFirstBranchPresentation I)
    (phi : Nat → Nat)
    (hphi : UniversalAuxBranchProperty G I E phi)
    {S₀ S₁ S₂ : Set CoordNode}
    {sigma : Nat → Nat}
    {r₀ : EnumNode (sigma 0)}
    {r₁ : OneNode (sigma 0)}
    {r₂ : AuxNode (sigma 0)}
    (hS₀ : FiniteStrongPicture S₀ sigma k (.enum (sigma 0) r₀))
    (hS₁ : FiniteStrongPicture S₁ sigma k (.one (sigma 0) r₁))
    (hS₂ : FiniteStrongPicture S₂ sigma k (.aux (sigma 0) r₂))
    (hsigma : StrictMono sigma)
    (A : EnumNode (k + 1))
    (hI : A.truncate n = I)
    (hfix : ∀ j < n, sigma j = j) :
    ∃ e : Ordered3Graph.Embedding A.toOrdered3Graph G.graph,
      e.AuxTypeRespecting ∧
      (∀ j : Nat, j < n → e j = j) ∧
      ∀ i : Fin (k + 1),
        ∃ hB : InRelativeBranchGraph I
            (finiteStrongPicture_branchMap hS₀ hS₁ hS₂
              (A.toOrdered3Graph.branchNode i.val)
              (Nat.le_of_lt_succ i.isLt)),
          e i.val =
            phi (E.code.symm
              (⟨finiteStrongPicture_branchMap hS₀ hS₁ hS₂
                  (A.toOrdered3Graph.branchNode i.val)
                  (Nat.le_of_lt_succ i.isLt), hB⟩ :
                RelativeBranchNode I)) := by
  obtain ⟨H, hH, eA, eG, hauxA, hauxG, hauxComp, hfixComp,
      hbranch, hindex⟩ :=
    exists_finiteStrong_actualAuxEmbedding_to_generic
      G I E phi hphi hS₀ hS₁ hS₂ hsigma A hI hfix
  refine ⟨eG.comp eA, hauxComp, hfixComp, ?_⟩
  intro i
  let B : EnumerationBranchNode :=
    finiteStrongPicture_branchMap hS₀ hS₁ hS₂
      (A.toOrdered3Graph.branchNode i.val)
      (Nat.le_of_lt_succ i.isLt)
  have hB : InRelativeBranchGraph I B := by
    change InRelativeBranchGraph I
      (finiteStrongPicture_branchMap hS₀ hS₁ hS₂
        (A.toOrdered3Graph.branchNode i.val)
        (Nat.le_of_lt_succ i.isLt))
    rw [hbranch i]
    exact H.branchNode_mem_relative I hH (eA i.val)
  refine ⟨hB, ?_⟩
  have heA : eA i.val = sigma i.val := by
    have hh := congrArg EnumerationBranchNode.last (hbranch i)
    change sigma i.val = eA i.val at hh
    exact hh.symm
  have hnode :
      (⟨B, hB⟩ : RelativeBranchNode I) =
        H.relativeBranchNode I hH (sigma i.val) := by
    apply Subtype.ext
    calc
      B = H.branchNode (eA i.val) := hbranch i
      _ = H.branchNode (sigma i.val) := by rw [heA]
  calc
    (eG.comp eA) i.val =
        phi (E.branchIndex H hH (sigma i.val)) := hindex i
    _ = phi (E.code.symm
          (H.relativeBranchNode I hH (sigma i.val))) := rfl
    _ = phi (E.code.symm (⟨B, hB⟩ : RelativeBranchNode I)) := by
      rw [← hnode]

end CoordNode
end ThreeUniformDiaries
