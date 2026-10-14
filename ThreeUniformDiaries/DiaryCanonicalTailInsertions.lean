import ThreeUniformDiaries.DiaryEnvelopeMinimality

/-!
# Canonical finite tail enumerations

Explicit strictly increasing maps which fix an arbitrary protected
prefix and select two endpoints, with or without their singleton
meet. The maps extend beyond the selected tails; the extension is
irrelevant to the envelope, but makes the functions legitimate
enumerations of all Nat.

No image-convexity or consecutive-target-level assumption is used.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Include two endpoints directly after the protected prefix and
continue with consecutive vertices after the second endpoint. -/
def twoTailInsertion (j a b t : Nat) : Nat :=
  if t < j then t
  else if t = j then a
  else b + (t - (j+1))

/-- Include first the singleton split, then its two leaf endpoints,
and continue consecutively after the last leaf. -/
def threeTailInsertion (j m a b t : Nat) : Nat :=
  if t < j then t
  else if t = j then m
  else if t = j+1 then a
  else b + (t - (j+2))

theorem twoTailInsertion_strictMono
    (j a b : Nat) (hja : j ≤ a) (hab : a < b) :
    StrictMono (twoTailInsertion j a b) := by
  apply strictMono_nat_of_lt_succ
  intro t
  unfold twoTailInsertion
  split_ifs <;> omega

theorem threeTailInsertion_strictMono
    (j m a b : Nat) (hjm : j ≤ m) (hma : m < a)
    (hab : a < b) :
    StrictMono (threeTailInsertion j m a b) := by
  apply strictMono_nat_of_lt_succ
  intro t
  unfold threeTailInsertion
  split_ifs <;> omega

theorem twoTailInsertion_fix_prefix
    (j a b t : Nat) (ht : t < j) :
    twoTailInsertion j a b t = t := by
  simp [twoTailInsertion, ht]

theorem threeTailInsertion_fix_prefix
    (j m a b t : Nat) (ht : t < j) :
    threeTailInsertion j m a b t = t := by
  simp [threeTailInsertion, ht]

theorem twoTailInsertion_first (j a b : Nat) :
    twoTailInsertion j a b j = a := by
  unfold twoTailInsertion
  split_ifs <;> omega

theorem twoTailInsertion_second (j a b : Nat) :
    twoTailInsertion j a b (j+1) = b := by
  unfold twoTailInsertion
  split_ifs <;> omega

theorem threeTailInsertion_split (j m a b : Nat) :
    threeTailInsertion j m a b j = m := by
  unfold threeTailInsertion
  split_ifs <;> omega

theorem threeTailInsertion_first (j m a b : Nat) :
    threeTailInsertion j m a b (j+1) = a := by
  unfold threeTailInsertion
  split_ifs <;> omega

theorem threeTailInsertion_second (j m a b : Nat) :
    threeTailInsertion j m a b (j+2) = b := by
  unfold threeTailInsertion
  split_ifs <;> omega

/-- The two-tail carrier has exactly the protected prefix
plus the two selected target endpoints. -/
theorem twoTailInsertion_carrier_iff
    (j a b x : Nat) :
    x ∈ selectedCarrier (twoTailInsertion j a b) (j+2) ↔
      x < j ∨ x = a ∨ x = b := by
  constructor
  · rintro ⟨t, ht, hval⟩
    by_cases hpre : t < j
    · left
      rw [twoTailInsertion_fix_prefix j a b t hpre] at hval
      omega
    · have hcases : t = j ∨ t = j+1 := by omega
      rcases hcases with h | h
      · right
        left
        rw [h, twoTailInsertion_first] at hval
        exact hval.symm
      · right
        right
        rw [h, twoTailInsertion_second] at hval
        exact hval.symm
  · intro hx
    rcases hx with hpre | ha | hb
    · exact ⟨x, by omega, twoTailInsertion_fix_prefix j a b x hpre⟩
    · exact ⟨j, by omega, (twoTailInsertion_first j a b).trans ha.symm⟩
    · exact ⟨j+1, by omega,
        (twoTailInsertion_second j a b).trans hb.symm⟩

/-- The three-tail carrier consists of precisely the full prefix,
the split, and the two distinguished leaves. -/
theorem threeTailInsertion_carrier_iff
    (j m a b x : Nat) :
    x ∈ selectedCarrier (threeTailInsertion j m a b) (j+3) ↔
      x < j ∨ x = m ∨ x = a ∨ x = b := by
  constructor
  · rintro ⟨t, ht, hval⟩
    by_cases hpre : t < j
    · left
      rw [threeTailInsertion_fix_prefix j m a b t hpre] at hval
      omega
    · have hcases : t = j ∨ t = j+1 ∨ t = j+2 := by omega
      rcases hcases with h | h | h
      · right; left
        rw [h, threeTailInsertion_split] at hval
        exact hval.symm
      · right; right; left
        rw [h, threeTailInsertion_first] at hval
        exact hval.symm
      · right; right; right
        rw [h, threeTailInsertion_second] at hval
        exact hval.symm
  · intro hx
    rcases hx with hpre | hm | ha | hb
    · exact ⟨x, by omega, threeTailInsertion_fix_prefix j m a b x hpre⟩
    · exact ⟨j, by omega, (threeTailInsertion_split j m a b).trans hm.symm⟩
    · exact ⟨j+1, by omega,
        (threeTailInsertion_first j m a b).trans ha.symm⟩
    · exact ⟨j+2, by omega,
        (threeTailInsertion_second j m a b).trans hb.symm⟩

end Ordered3Graph
end ThreeUniformDiaries
