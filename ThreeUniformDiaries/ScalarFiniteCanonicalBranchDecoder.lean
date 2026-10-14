import ThreeUniformDiaries.ScalarCanonicalFinitePictures
import ThreeUniformDiaries.FiniteCanonicalBranchMap

/-!
# The actual F_I branch value of a finite scalar approximation

The geometric finite decoder supplies real E0/E1/E2 strong pictures
on a unique finite carrier and on the canonical selected level map,
but presents three proofs and three coordinate root witnesses.

A finite strong picture has a unique root on its carrier, so the
canonical maps (and the finite F_I last-vertex successor formula)
cannot depend on those remaining witnesses. Using proof irrelevance
we define a genuine Option-valued finite branch action directly
on Milliken's finite approximation object.

It maps any approximation without the extra scalar root to `none`,
and all rooted approximations to the actual branch value. The
relative K_I preservation is proved separately for anchored stems.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Milliken
open Milliken.GeneralTree
open ThreeUniformDiaries.CoordNode

/-- Two finite strong-picture descriptions of the same set have
the same actual coordinate-tree root. -/
theorem finiteStrongPicture_root_unique
    {S : Set CoordNode} {f : Nat → Nat} {k : Nat}
    {r s : CoordNode}
    (hR : FiniteStrongPicture S f k r)
    (hS : FiniteStrongPicture S f k s) :
    r = s := by
  obtain ⟨_, _, hr, hrle, _, _, _⟩ := hR
  obtain ⟨_, _, hs, hsle, _, _, _⟩ := hS
  exact _root_.le_antisymm (hrle s hs) (hsle r hr)

/-- In the enum coordinate, selected finite roots are determined
by the carrier and not by a classical choice of their records. -/
theorem finiteStrongPicture_enum_root_unique
    {S : Set CoordNode} {f : Nat → Nat} {k : Nat}
    {a b : EnumNode (f 0)}
    (ha : FiniteStrongPicture S f k (.enum (f 0) a))
    (hb : FiniteStrongPicture S f k (.enum (f 0) b)) :
    a = b := by
  have h := finiteStrongPicture_root_unique ha hb
  injection h

theorem finiteStrongPicture_one_root_unique
    {S : Set CoordNode} {f : Nat → Nat} {k : Nat}
    {a b : OneNode (f 0)}
    (ha : FiniteStrongPicture S f k (.one (f 0) a))
    (hb : FiniteStrongPicture S f k (.one (f 0) b)) :
    a = b := by
  have h := finiteStrongPicture_root_unique ha hb
  injection h

theorem finiteStrongPicture_aux_root_unique
    {S : Set CoordNode} {f : Nat → Nat} {k : Nat}
    {a b : AuxNode (f 0)}
    (ha : FiniteStrongPicture S f k (.aux (f 0) a))
    (hb : FiniteStrongPicture S f k (.aux (f 0) b)) :
    a = b := by
  have h := finiteStrongPicture_root_unique ha hb
  injection h

/-- The actual finite F_I branch value is independent of which
proofs and coordinate root witnesses were used to realize the
same three finite strong pictures. -/
theorem finiteStrongPicture_branchMap_witness_independent
    {S₀ S₁ S₂ : Set CoordNode} {f : Nat → Nat} {k : Nat}
    {r₀ q₀ : EnumNode (f 0)}
    {r₁ q₁ : OneNode (f 0)}
    {r₂ q₂ : AuxNode (f 0)}
    (h₀ : FiniteStrongPicture S₀ f k (.enum (f 0) r₀))
    (h₁ : FiniteStrongPicture S₁ f k (.one (f 0) r₁))
    (h₂ : FiniteStrongPicture S₂ f k (.aux (f 0) r₂))
    (g₀ : FiniteStrongPicture S₀ f k (.enum (f 0) q₀))
    (g₁ : FiniteStrongPicture S₁ f k (.one (f 0) q₁))
    (g₂ : FiniteStrongPicture S₂ f k (.aux (f 0) q₂))
    (B : EnumerationBranchNode) (hB : B.last ≤ k) :
    finiteStrongPicture_branchMap h₀ h₁ h₂ B hB =
      finiteStrongPicture_branchMap g₀ g₁ g₂ B hB := by
  have he₀ := finiteStrongPicture_enum_root_unique h₀ g₀
  have he₁ := finiteStrongPicture_one_root_unique h₁ g₁
  have he₂ := finiteStrongPicture_aux_root_unique h₂ g₂
  cases he₀
  cases he₁
  cases he₂
  rfl

/-- Real witness data for the canonical finite scalar approximation
code. All fields depend only on the carrier and finite heights of a;
the remaining root/proof witnesses are provably unique up to Prop
proof irrelevance. -/
structure CanonicalFinitePictures
    (k : Nat)
    (a : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2)) where
  r₀ : EnumNode (canonicalFiniteLevelMap k a 0)
  r₁ : OneNode (canonicalFiniteLevelMap k a 0)
  r₂ : AuxNode (canonicalFiniteLevelMap k a 0)
  h₀ : FiniteStrongPicture ((finiteTypedCarrier k a).carrier 0)
    (canonicalFiniteLevelMap k a) k
    (.enum (canonicalFiniteLevelMap k a 0) r₀)
  h₁ : FiniteStrongPicture ((finiteTypedCarrier k a).carrier 1)
    (canonicalFiniteLevelMap k a) k
    (.one (canonicalFiniteLevelMap k a 0) r₁)
  h₂ : FiniteStrongPicture ((finiteTypedCarrier k a).carrier 2)
    (canonicalFiniteLevelMap k a) k
    (.aux (canonicalFiniteLevelMap k a 0) r₂)

/-- Choose actual finite pictures from the proved existence result;
the branch action below does not depend on which choice is made. -/
noncomputable def chooseFinitePictures
    (k : Nat)
    (a : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2))
    (hroot : (none : WithBot CoordNode) ∈ a.carrier) :
    CanonicalFinitePictures k a :=
  Classical.choice (by
    obtain ⟨r₀, r₁, r₂, h₀, h₁, h₂⟩ :=
      finiteCode_has_canonical_pictures k a hroot
    exact ⟨⟨r₀, r₁, r₂, h₀, h₁, h₂⟩⟩)

/-- The actual last-vertex F_I branch action, evaluated on a finite
scalar Milliken approximation containing the newly added root. -/
noncomputable def rootedScalarFiniteBranchMap
    (k : Nat)
    (a : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2))
    (hroot : (none : WithBot CoordNode) ∈ a.carrier)
    (B : EnumerationBranchNode) (hB : B.last ≤ k) :
    EnumerationBranchNode :=
  let C := chooseFinitePictures k a hroot
  finiteStrongPicture_branchMap C.h₀ C.h₁ C.h₂ B hB

/-- The branch value agrees with that computed from ANY other
genuine finite picture witnesses for the same approximation.
Therefore neither the classical choice nor the proof of rootedness
can alter any encoded K_I vertex. -/
theorem rootedScalarFiniteBranchMap_eq_of_pictures
    (k : Nat)
    (a : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2))
    (hroot : (none : WithBot CoordNode) ∈ a.carrier)
    {r₀ : EnumNode (canonicalFiniteLevelMap k a 0)}
    {r₁ : OneNode (canonicalFiniteLevelMap k a 0)}
    {r₂ : AuxNode (canonicalFiniteLevelMap k a 0)}
    (h₀ : FiniteStrongPicture ((finiteTypedCarrier k a).carrier 0)
      (canonicalFiniteLevelMap k a) k
      (.enum (canonicalFiniteLevelMap k a 0) r₀))
    (h₁ : FiniteStrongPicture ((finiteTypedCarrier k a).carrier 1)
      (canonicalFiniteLevelMap k a) k
      (.one (canonicalFiniteLevelMap k a 0) r₁))
    (h₂ : FiniteStrongPicture ((finiteTypedCarrier k a).carrier 2)
      (canonicalFiniteLevelMap k a) k
      (.aux (canonicalFiniteLevelMap k a 0) r₂))
    (B : EnumerationBranchNode) (hB : B.last ≤ k) :
    rootedScalarFiniteBranchMap k a hroot B hB =
      finiteStrongPicture_branchMap h₀ h₁ h₂ B hB := by
  exact finiteStrongPicture_branchMap_witness_independent
    (chooseFinitePictures k a hroot).h₀
    (chooseFinitePictures k a hroot).h₁
    (chooseFinitePictures k a hroot).h₂
    h₀ h₁ h₂ B hB

/-- The total Option-valued scalar finite branch decoder: invalid
rootless approximations receive no branch code. -/
noncomputable def decodeFiniteBranch
    (k : Nat)
    (a : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2))
    (B : EnumerationBranchNode) (hB : B.last ≤ k) :
    Option EnumerationBranchNode := by
  classical
  exact if h : (none : WithBot CoordNode) ∈ a.carrier then
    some (rootedScalarFiniteBranchMap k a h B hB)
  else none

theorem decodeFiniteBranch_root
    (k : Nat)
    (a : FiniteApprox CoordNode.rootGluedAmbientTree (k + 2))
    (B : EnumerationBranchNode) (hB : B.last ≤ k)
    (hroot : (none : WithBot CoordNode) ∈ a.carrier) :
    decodeFiniteBranch k a B hB =
      some (rootedScalarFiniteBranchMap k a hroot B hB) := by
  classical
  simp only [decodeFiniteBranch, dite_eq_left hroot]

end ATRFiniteDecoder
end ThreeUniformDiaries
