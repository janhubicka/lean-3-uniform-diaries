import ThreeUniformDiaries.FiniteCanonicalBranchCode
import ThreeUniformDiaries.FiniteOneCanonicalCandidateIdentity
import ThreeUniformDiaries.FiniteEnumCanonicalCandidateIdentity
import ThreeUniformDiaries.FiniteAuxCanonicalRootIdentity
import ThreeUniformDiaries.FiniteCanonicalOneEnumRootIdentities
import ThreeUniformDiaries.FiniteAuxCanonicalCandidateIdentity

/-!
# Simultaneous finite Aemb coordinate identities for typed strong pictures

The roots and prescribed nodes of the three coordinate trees determine
all canonical maps, so no separate root or type compatibility axioms
are needed. Under a genuine finite aux-type-respecting embedding, three
typed finite strong pictures containing E0/E1/E2^- suffice to prove:

* the constructed f₂ maps every actual source auxiliary type to its
  corresponding selected target auxiliary type;
* the constructed f₁ maps all actual source singleton types similarly;
* the constructed f₀ maps every source enumeration prefix to the target
  prefix at the selected level;
* the F_I^S code of each source branch vertex is literally H|f(i)+1.

This is the complete *coding-identity* part of finite Aemb, conditional
only on the existence of typed strong pictures with candidate inclusion.
The latter existence and the countable-target restriction are tracked
separately, to avoid silently strengthening finite embedding hypotheses.
-/

namespace ThreeUniformDiaries
namespace EnumNode

theorem finiteAemb_canonical_images_of_typed_pictures
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (f : Nat → Nat)
    (hf : Ordered3Graph.FiniteAuxEmbedding
      A.toOrdered3Graph H.toOrdered3Graph f m)
    (n : Nat) (hm : 0 < m)
    (hfix : ∀ j < n, f j = j)
    {S₀ S₁ S₂ : Set CoordNode}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : CoordNode.FiniteStrongPicture S₀ f (m - 1)
      (.enum (f 0) r₀))
    (h₁ : CoordNode.FiniteStrongPicture S₁ f (m - 1)
      (.one (f 0) r₁))
    (h₂ : CoordNode.FiniteStrongPicture S₂ f (m - 1)
      (.aux (f 0) r₂))
    (hinc₀ : ∀ x, finiteEnumCandidate H f n m x → x ∈ S₀)
    (hinc₁ : ∀ x, finiteOneCandidate A H f n x → x ∈ S₁)
    (hinc₂ : ∀ x, finiteAuxCandidate A H f n x → x ∈ S₂) :
    (∀ (i u v : Nat) (hiu : i ≤ u) (huv : u < v)
      (hvm : v < m),
      (CoordNode.finiteStrongPicture_auxCanonicalMap h₂ i
        (by omega) (A.auxType i u v)).val =
          H.auxType (f i) (f u) (f v)) ∧
    (∀ (i v : Nat) (hiv : i ≤ v) (hvm : v < m),
      (CoordNode.finiteStrongPicture_oneCanonicalMap h₁ h₂ i
        (by omega) (A.oneType i v)).val =
          H.oneType (f i) (f v)) ∧
    (∀ (i : Nat) (him : i < m),
      (CoordNode.finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ i
        (by omega) (A.truncate i)).val =
          H.truncate (f i)) ∧
    (∀ (i : Nat) (him : i < m),
      (CoordNode.finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ i
        (by omega) (A.truncate i)).val.succ
        (CoordNode.finiteStrongPicture_oneCanonicalMap h₁ h₂ i
          (by omega) (A.oneType i i)).val =
        H.truncate (f i + 1)) := by
  have hroot₂ : ∀ u v : Nat, u < v → v < m →
      r₂ = H.auxType (f 0) (f u) (f v) := by
    intro u v huv hvm
    exact A.finiteAuxCandidate_root_eq_pairType
      H f n hfix h₂ hinc₂ u v huv hvm
  have hAux : ∀ (i u v : Nat) (hiu : i ≤ u)
      (huv : u < v) (hvm : v < m),
      (CoordNode.finiteStrongPicture_auxCanonicalMap h₂ i
        (by omega) (A.auxType i u v)).val =
        H.auxType (f i) (f u) (f v) := by
    intro i u v hiu huv hvm
    exact A.finiteAuxCanonicalMap_prescribed_pairTypes
      H f hf n hfix h₂ hinc₂ hroot₂ i u v hiu huv hvm
  have hroot₁ : ∀ v : Nat, v < m →
      r₁ = H.oneType (f 0) (f v) := by
    intro v hvm
    exact A.finiteOneCandidate_root_eq_vertexType
      H f n hfix h₁ hinc₁ v hvm
  have hOne : ∀ (i v : Nat) (hiv : i ≤ v) (hvm : v < m),
      (CoordNode.finiteStrongPicture_oneCanonicalMap h₁ h₂ i
        (by omega) (A.oneType i v)).val =
        H.oneType (f i) (f v) := by
    intro i v hiv hvm
    apply A.finiteOneCanonicalMap_prescribed_vertexTypes
      H f hf n hfix h₁ h₂ hinc₁ hroot₁
      (fun j v hjv hvm => hAux j j v (le_refl j) hjv hvm)
      i v hiv hvm
  have hroot₀ : r₀ = H.truncate (f 0) :=
    finiteEnumCandidate_root_eq_initialSegment
      H f n m hm hfix h₀ hinc₀
  have hEnum : ∀ (i : Nat) (him : i < m),
      (CoordNode.finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ i
        (by omega) (A.truncate i)).val =
          H.truncate (f i) := by
    intro i him
    exact A.finiteEnumCanonicalMap_prescribed_prefixes
      H f hf.strictMono n hfix h₀ h₁ h₂ hinc₀ hroot₀
      (fun j hjm => hOne j j (le_refl j) hjm)
      i him
  refine ⟨hAux, hOne, hEnum, ?_⟩
  intro i him
  exact A.finiteCanonical_branch_code_of_coordinates
    H h₀ h₁ h₂ i (by omega)
    (hEnum i him) (hOne i i (le_refl i) him)

end EnumNode
end ThreeUniformDiaries
