import ThreeUniformDiaries.FiniteEncoderMeetLevels
import ThreeUniformDiaries.TypeNodePrefix

/-!
# Meet closure of the selected 1-type nodes in the finite encoder

The E1 coordinate of manuscript Lemma Aemb contains every singleton
type node below the fixed prefix n and, at selected level e(i), the
1-type of every source vertex v >= i. The tree meet of two such
selected nodes is another selected node: its level is
e(min(i,j,oneMeet_A(v,w))) and its contents are the truncation of
one input 1-type.

This proof uses the actual CoordNode.meet operation. It does not
assume a strong-subtree completion theorem.
-/

namespace ThreeUniformDiaries
namespace EnumNode

/-- The E1 candidate set in the manuscript's finite encoding. -/
def finiteOneCandidate
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (e : Ordered3Graph.Embedding A.toOrdered3Graph H.toOrdered3Graph)
    (n : Nat) (x : CoordNode) : Prop :=
  (∃ (k : Nat) (B : OneNode k),
    k < n ∧ x = CoordNode.one k B) ∨
  (∃ i v : Nat,
    n ≤ i ∧ i ≤ v ∧ v < m ∧
      x = CoordNode.one (e i) (H.oneType (e i) (e v)))

private theorem oneMeet_prefix_left
    (n i j : Nat) (B : OneNode i) (C : OneNode j)
    (hi : i < n) :
    ∃ (k : Nat) (D : OneNode k),
      k < n ∧
        CoordNode.meet (.one i B) (.one j C) = .one k D := by
  let k := CoordNode.meetLevel (.one i B) (.one j C)
  refine ⟨k, B.truncate k, ?_, rfl⟩
  exact lt_of_le_of_lt (CoordNode.meetLevel_le_left _ _) hi

private theorem oneMeet_prefix_right
    (n i j : Nat) (B : OneNode i) (C : OneNode j)
    (hj : j < n) :
    ∃ (k : Nat) (D : OneNode k),
      k < n ∧
        CoordNode.meet (.one i B) (.one j C) = .one k D := by
  let k := CoordNode.meetLevel (.one i B) (.one j C)
  refine ⟨k, B.truncate k, ?_, rfl⟩
  exact lt_of_le_of_lt (CoordNode.meetLevel_le_right _ _) hj

/-- The E1 candidate set really is closed under the ambient tree meet.
The initial segment is required to be fixed pointwise, exactly as in
the finite strong-subtree encoding lemma. -/
theorem finiteOneCandidate_meet
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (e : Ordered3Graph.Embedding A.toOrdered3Graph H.toOrdered3Graph)
    (haux : e.AuxTypeRespecting)
    (n : Nat) (hfix : ∀ k : Nat, k < n → e k = k)
    (x y : CoordNode)
    (hx : finiteOneCandidate A H e n x)
    (hy : finiteOneCandidate A H e n y) :
    finiteOneCandidate A H e n (CoordNode.meet x y) := by
  rcases hx with ⟨i, B, hi, rfl⟩ | ⟨i, v, hni, hiv, hv, rfl⟩
  · rcases hy with ⟨j, C, hj, rfl⟩ | ⟨j, w, hnj, hjw, hw, rfl⟩
    · exact Or.inl (oneMeet_prefix_left n i j B C hi)
    · exact Or.inl
        (oneMeet_prefix_left n i (e j) B
          (H.oneType (e j) (e w)) hi)
  · rcases hy with ⟨j, C, hj, rfl⟩ | ⟨j, w, hnj, hjw, hw, rfl⟩
    · exact Or.inl
        (oneMeet_prefix_right n (e i) j
          (H.oneType (e i) (e v)) C hj)
    · let k := min (min i j) (A.toOrdered3Graph.oneMeetLevel v w)
      have hk : k ≤ i :=
        (min_le_left (min i j) _).trans (min_le_left i j)
      have hkv : k ≤ v := hk.trans hiv
      have hlev :
          CoordNode.meetLevel
            (.one (e i) (H.oneType (e i) (e v)))
            (.one (e j) (H.oneType (e j) (e w))) = e k :=
        H.selectedOne_meetLevel A e haux i j v w hiv hjw
      have hmeet :
          CoordNode.meet
            (.one (e i) (H.oneType (e i) (e v)))
            (.one (e j) (H.oneType (e j) (e w))) =
            .one (e k) (H.oneType (e k) (e v)) := by
        calc
          CoordNode.meet
              (.one (e i) (H.oneType (e i) (e v)))
              (.one (e j) (H.oneType (e j) (e w))) =
              .one (e k)
                ((H.oneType (e i) (e v)).truncate (e k)) := by
                  simp only [CoordNode.meet, CoordNode.truncate, hlev]
          _ = .one (e k) (H.oneType (e k) (e v)) := by
              rw [H.oneType_truncate (u := e v)
                (e.strictMono.monotone hk)]
      by_cases hkn : k < n
      · left
        have heq : e k = k := hfix k hkn
        rw [heq] at hmeet
        exact ⟨k, H.oneType k (e v), hkn, hmeet⟩
      · right
        exact ⟨k, v, Nat.le_of_not_gt hkn, hkv, hv, hmeet⟩

end EnumNode
end ThreeUniformDiaries
