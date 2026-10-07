import ThreeUniformDiaries.VectorTree

/-!
# Uniqueness of the three type-tree successor parameters

This verifies the uniqueness claim following the three successor operations
in Section 4 of the 3-uniform diaries manuscript.  Every successor node
determines both its predecessor and its newly added parameter.

The converses are immediate by substituting the equality of the two
parameters.
-/

namespace ThreeUniformDiaries

namespace AuxNode

theorem succ_eq_iff {n : Nat} (a b : AuxNode n) (e f : Bool) :
    a.succ e = b.succ f ↔ a = b ∧ e = f := by
  constructor
  · intro h
    constructor
    · have hpred := congrArg (fun x : AuxNode (n + 1) => x.truncate n) h
      simpa using hpred
    · have hbit := congrArg (fun x : AuxNode (n + 1) => x.bit n) h
      simpa using hbit
  · rintro ⟨rfl, rfl⟩
    rfl

end AuxNode

namespace OneNode

theorem succ_eq_iff {n : Nat}
    (a b : OneNode n) (c d : AuxNode n) :
    a.succ c = b.succ d ↔ a = b ∧ c = d := by
  constructor
  · intro h
    constructor
    · have hpred := congrArg (fun x : OneNode (n + 1) => x.truncate n) h
      simpa using hpred
    · have hparam := congrArg (fun x : OneNode (n + 1) => x.boundaryAux n) h
      simpa using hparam
  · rintro ⟨rfl, rfl⟩
    rfl

end OneNode

namespace EnumNode

theorem succ_eq_iff {n : Nat}
    (a b : EnumNode n) (c d : OneNode n) :
    a.succ c = b.succ d ↔ a = b ∧ c = d := by
  constructor
  · intro h
    constructor
    · have hpred := congrArg (fun x : EnumNode (n + 1) => x.truncate n) h
      simpa using hpred
    · have hparam := congrArg (fun x : EnumNode (n + 1) => x.boundaryOne n) h
      simpa using hparam
  · rintro ⟨rfl, rfl⟩
    rfl

end EnumNode

end ThreeUniformDiaries
