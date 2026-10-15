import ThreeUniformDiaries.DiaryPrediaryTypeCode

/-!
# Local progress of an inserted old-type class indicator

The manuscript's 1-split insertion picks a class of OLD types
at the next cut. Inserting its indicator at n has two simultaneous
properties:

* every pre-existing old type partition at a later fixed
  source cut k > n remains unchanged;
* two chosen witnesses which agree below n but disagree at n+1
  are now separated by the FRESH coordinate n.

This is the precise, formalised local progress calculation.
It does NOT establish that all bad meets are repaired in a
finite number of steps or that diary V/E axioms are preserved.
-/

namespace ThreeUniformDiaries
namespace PrediaryCode

variable {α : Type*}

theorem prefixEq_refl (ty : α → Nat → Bool)
    (n : Nat) (a : α) :
    PrefixEq ty n a a := by
  intro j hj
  rfl

theorem prefixEq_symm (ty : α → Nat → Bool)
    (n : Nat) (a b : α)
    (hab : PrefixEq ty n a b) :
    PrefixEq ty n b a := by
  intro j hj
  exact (hab j hj).symm

theorem prefixEq_trans (ty : α → Nat → Bool)
    (n : Nat) (a b c : α)
    (hab : PrefixEq ty n a b)
    (hbc : PrefixEq ty n b c) :
    PrefixEq ty n a c := by
  intro j hj
  exact (hab j hj).trans (hbc j hj)

/-- The new bit selects precisely the OLD prefix class of a. -/
noncomputable def selectedClassBit
    (ty : α → Nat → Bool) (n : Nat) (a u : α) : Bool := by
  classical
  exact decide (PrefixEq ty (n + 1) a u)

/-- The selected old class is constant on all old (n+1)-types. -/
theorem selectedClassBit_factors
    (ty : α → Nat → Bool) (n : Nat) (a u v : α)
    (huv : PrefixEq ty (n + 1) u v) :
    selectedClassBit ty n a u = selectedClassBit ty n a v := by
  classical
  have hiff :
      PrefixEq ty (n + 1) a u ↔ PrefixEq ty (n + 1) a v := by
    constructor
    · intro h
      exact prefixEq_trans ty (n+1) a u v h huv
    · intro h
      exact prefixEq_trans ty (n+1) a v u h
        (prefixEq_symm ty (n+1) u v huv)
  by_cases hp : PrefixEq ty (n + 1) a u
  · have hq := hiff.mp hp
    simp [selectedClassBit, hp, hq]
  · have hq : ¬ PrefixEq ty (n + 1) a v := by
      intro hv
      exact hp (hiff.mpr hv)
    simp [selectedClassBit, hp, hq]

theorem selectedClassBit_self
    (ty : α → Nat → Bool) (n : Nat) (a : α) :
    selectedClassBit ty n a a = true := by
  classical
  have hs := prefixEq_refl ty (n+1) a
  simp [selectedClassBit, hs]

theorem selectedClassBit_other
    (ty : α → Nat → Bool) (n : Nat) (a b : α)
    (hdiff : ¬ PrefixEq ty (n + 1) a b) :
    selectedClassBit ty n a b = false := by
  classical
  simp [selectedClassBit, hdiff]

/-- Every old fixed-cut partition is unchanged by this
specific class-indicator insertion, however many old points
belong to the family. -/
theorem selectedClassBit_fixedCut_iff
    (ty : α → Nat → Bool) (n k : Nat) (a u v : α)
    (hnk : n < k) :
    PrefixEq (insertBit ty n (selectedClassBit ty n a))
      (k + 1) u v ↔ PrefixEq ty k u v := by
  apply prefixEq_insert_iff_of_factor ty n k
    (selectedClassBit ty n a) u v hnk
  intro x y h
  exact selectedClassBit_factors ty n a x y h

/-- All agreements before the new coordinate are unaffected. -/
theorem insertBit_preserves_prefix_below
    (ty : α → Nat → Bool) (n : Nat)
    (newBit : α → Bool) (a b : α)
    (h : PrefixEq ty n a b) :
    PrefixEq (insertBit ty n newBit) n a b := by
  intro j hj
  simp only [insertBit, if_pos hj]
  exact h j hj

/-- A previously defective pair is now separated by the
fresh split at n, while retaining its old common prefix. -/
theorem selectedClassBit_repairs_witness_at_cut
    (ty : α → Nat → Bool) (n : Nat) (a b : α)
    (hsame : PrefixEq ty n a b)
    (hdiff : ¬ PrefixEq ty (n + 1) a b) :
    PrefixEq (insertBit ty n (selectedClassBit ty n a))
      n a b ∧
    ¬ PrefixEq (insertBit ty n (selectedClassBit ty n a))
      (n + 1) a b := by
  constructor
  · exact insertBit_preserves_prefix_below ty n
      (selectedClassBit ty n a) a b hsame
  · intro h
    have hn := h n (by omega)
    have ha := selectedClassBit_self ty n a
    have hb := selectedClassBit_other ty n a b hdiff
    simp only [insertBit, if_neg (by omega : ¬ n < n),
      if_pos rfl, ha, hb] at hn
    cases hn

end PrediaryCode
end ThreeUniformDiaries
