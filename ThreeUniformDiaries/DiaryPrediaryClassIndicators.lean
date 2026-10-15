import ThreeUniformDiaries.AuxTypes
import ThreeUniformDiaries.DiaryPrediaryTypeCode

/-!
# Old type-class indicator bits for pre-diary insertion

At a defective 1-split, the manuscript adds edges incident
with the new vertex precisely to leaves in one OLD
singleton-type class at ell+1. At a defective 2-split it
likewise selects one OLD full pair-type class.

The essential finite-type invariant is that membership in
a fixed equivalence class factors through that equivalence
relation. We verify this statement directly for the actual
singleton and full pair-type predicates of ordered
3-uniform hypergraphs (not a synthetic arbitrary partition).

This does not prove that inserting these edges preserves
the V/E diary conditions, protected meets or termination;
the factorisation is one needed ingredient only.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Singleton type agreement is symmetric at a fixed cut. -/
theorem oneTypeBelow_symm
    (H : Ordered3Graph Nat) (ell a b : Nat)
    (hab : H.SameOneTypeBelow ell a b) :
    H.SameOneTypeBelow ell b a := by
  intro i j hij hj
  exact (hab hij hj).symm

/-- Singleton type agreement is transitive. -/
theorem oneTypeBelow_trans
    (H : Ordered3Graph Nat) (ell a b c : Nat)
    (hab : H.SameOneTypeBelow ell a b)
    (hbc : H.SameOneTypeBelow ell b c) :
    H.SameOneTypeBelow ell a c := by
  intro i j hij hj
  exact (hab hij hj).trans (hbc hij hj)

/-- Auxiliary pair-type agreement is symmetric. -/
theorem auxTypeBelow_symm
    (H : Ordered3Graph Nat) (ell a b c d : Nat)
    (hab : H.SameAuxTypeBelow ell a b c d) :
    H.SameAuxTypeBelow ell c d a b := by
  intro i hi
  exact (hab hi).symm

/-- Auxiliary pair-type agreement is transitive. -/
theorem auxTypeBelow_trans
    (H : Ordered3Graph Nat) (ell a b c d e f : Nat)
    (hab : H.SameAuxTypeBelow ell a b c d)
    (hbc : H.SameAuxTypeBelow ell c d e f) :
    H.SameAuxTypeBelow ell a b e f := by
  intro i hi
  exact (hab hi).trans (hbc hi)

/-- Full ordered-pair type agreement is symmetric. -/
theorem twoTypeBelow_symm
    (H : Ordered3Graph Nat) (ell a b c d : Nat)
    (hab : H.SameTwoTypeBelow ell a b c d) :
    H.SameTwoTypeBelow ell c d a b := by
  rcases hab with ⟨h0,h1,ha⟩
  exact ⟨H.oneTypeBelow_symm ell a c h0,
    H.oneTypeBelow_symm ell b d h1,
    H.auxTypeBelow_symm ell a b c d ha⟩

/-- Full ordered-pair type agreement is transitive. -/
theorem twoTypeBelow_trans
    (H : Ordered3Graph Nat) (ell a b c d e f : Nat)
    (hab : H.SameTwoTypeBelow ell a b c d)
    (hbc : H.SameTwoTypeBelow ell c d e f) :
    H.SameTwoTypeBelow ell a b e f := by
  rcases hab with ⟨h0,h1,ha⟩
  rcases hbc with ⟨h0',h1',ha'⟩
  exact ⟨H.oneTypeBelow_trans ell a c e h0 h0',
    H.oneTypeBelow_trans ell b d f h1 h1',
    H.auxTypeBelow_trans ell a b c d e f ha ha'⟩

/-- The Boolean indicator of a selected old singleton-type
class at level ell+1. -/
noncomputable def oneClassBit
    (H : Ordered3Graph Nat) (ell a u : Nat) : Bool :=
  decide (H.SameOneTypeBelow (ell+1) a u)

/-- The fresh 1-split bit really depends only on an OLD
singleton-type class, exactly as demanded by factorisation. -/
theorem oneClassBit_factors
    (H : Ordered3Graph Nat) (ell a u v : Nat)
    (huv : H.SameOneTypeBelow (ell+1) u v) :
    H.oneClassBit ell a u = H.oneClassBit ell a v := by
  classical
  have hiff :
      H.SameOneTypeBelow (ell+1) a u ↔
      H.SameOneTypeBelow (ell+1) a v := by
    constructor
    · intro h
      exact H.oneTypeBelow_trans (ell+1) a u v h huv
    · intro h
      exact H.oneTypeBelow_trans (ell+1) a v u h
        (H.oneTypeBelow_symm (ell+1) u v huv)
  exact congrArg decide (propext hiff)

/-- The Boolean indicator of a selected old ordered-pair
type class at level ell+1. -/
noncomputable def twoClassBit
    (H : Ordered3Graph Nat)
    (ell a b u v : Nat) : Bool :=
  decide (H.SameTwoTypeBelow (ell+1) a b u v)

/-- The fresh 2-split bit factors through the OLD full
pair type at ell+1. -/
theorem twoClassBit_factors
    (H : Ordered3Graph Nat)
    (ell a b u v w x : Nat)
    (huv : H.SameTwoTypeBelow (ell+1) u v w x) :
    H.twoClassBit ell a b u v =
      H.twoClassBit ell a b w x := by
  classical
  have hiff :
      H.SameTwoTypeBelow (ell+1) a b u v ↔
      H.SameTwoTypeBelow (ell+1) a b w x := by
    constructor
    · intro h
      exact H.twoTypeBelow_trans (ell+1) a b u v w x h huv
    · intro h
      exact H.twoTypeBelow_trans (ell+1) a b w x u v h
        (H.twoTypeBelow_symm (ell+1) u v w x huv)
  exact congrArg decide (propext hiff)

end Ordered3Graph
end ThreeUniformDiaries
