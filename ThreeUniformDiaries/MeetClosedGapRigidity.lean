import ThreeUniformDiaries.TreeMeetTerminalExtension

/-!
# A meet-closed finite picture cannot duplicate a successor direction

Suppose S has no occupied levels strictly between l and L. Two nodes
of S on level L cannot both pass through the same node t of a level
strictly between l and L unless they are equal. Otherwise their
ambient-tree meet would be a member of S on a forbidden intervening
level. This is the key local uniqueness fact needed to extend a
meet-closed picture to a strong subtree with the same level set.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Meet-closed pictures cannot contain two distinct upper-level nodes
which share a predecessor strictly above the preceding selected level. -/
theorem unique_above_selected_gap
    (S : Set CoordNode) (hS : MeetClosed S)
    (l L : Nat) (hll : l < L)
    (hlevels : ∀ x ∈ S, level x ≤ l ∨ L ≤ level x)
    (a b t : CoordNode)
    (ha : a ∈ S) (hb : b ∈ S)
    (hla : level a = L) (hlb : level b = L)
    (hta : t ≤ a) (htb : t ≤ b)
    (hlt : l < level t) :
    a = b := by
  let q := meet a b
  have hcommon : ∃ c : CoordNode, c ≤ a ∧ c ≤ b :=
    ⟨t, hta, htb⟩
  have hqS : q ∈ S := hS ha hb
  have htq : t ≤ q := le_meet hta htb
  have hqA : q ≤ a := meet_le_left hcommon
  have hqB : q ≤ b := meet_le_right hcommon
  have hqHigh : L ≤ level q := by
    rcases hlevels q hqS with hlow | hhigh
    · have htql : level t ≤ level q := level_le_of_le htq
      omega
    · exact hhigh
  have hqLevel : level q = L := by
    have hqLow : level q ≤ level a := level_le_of_le hqA
    omega
  have hEqA : q = a :=
    eq_of_le_of_level_eq hqA (hqLevel.trans hla.symm)
  have hEqB : q = b :=
    eq_of_le_of_level_eq hqB (hqLevel.trans hlb.symm)
  exact hEqA.symm.trans hEqB

end CoordNode
end ThreeUniformDiaries
