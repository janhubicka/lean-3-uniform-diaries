import ThreeUniformDiaries.FiniteOneMeetClosure

/-!
# Meet closure of selected auxiliary types in the finite encoder

The E2 coordinate begins with all auxiliary-type nodes at levels
below the fixed prefix n. Its selected nodes at level e(i) are the
auxiliary types of original pairs u0 < u1 with i <= u0.
A pair of selected nodes has meet level
e(min(i,j,auxMeet_A(pair,pair'))), and its node is the matching
truncation, again present in the candidate set.

This lemma addresses E2 minus the optional terminal auxiliary node;
adding that terminal node must be treated separately.
-/

namespace ThreeUniformDiaries
namespace EnumNode

/-- The E2^- candidate set, before the optional final type node. -/
def finiteAuxCandidate
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (e : Ordered3Graph.Embedding A.toOrdered3Graph H.toOrdered3Graph)
    (n : Nat) (x : CoordNode) : Prop :=
  (∃ (k : Nat) (B : AuxNode k),
    k < n ∧ x = CoordNode.aux k B) ∨
  (∃ i u₀ u₁ : Nat,
    n ≤ i ∧ i ≤ u₀ ∧ u₀ < u₁ ∧ u₁ < m ∧
      x = CoordNode.aux (e i)
        (H.auxType (e i) (e u₀) (e u₁)))

private theorem auxMeet_prefix_left
    (n i j : Nat) (B : AuxNode i) (C : AuxNode j)
    (hi : i < n) :
    ∃ (k : Nat) (D : AuxNode k),
      k < n ∧
        CoordNode.meet (.aux i B) (.aux j C) = .aux k D := by
  let k := CoordNode.meetLevel (.aux i B) (.aux j C)
  refine ⟨k, B.truncate k, ?_, rfl⟩
  exact lt_of_le_of_lt (CoordNode.meetLevel_le_left _ _) hi

private theorem auxMeet_prefix_right
    (n i j : Nat) (B : AuxNode i) (C : AuxNode j)
    (hj : j < n) :
    ∃ (k : Nat) (D : AuxNode k),
      k < n ∧
        CoordNode.meet (.aux i B) (.aux j C) = .aux k D := by
  let k := CoordNode.meetLevel (.aux i B) (.aux j C)
  refine ⟨k, B.truncate k, ?_, rfl⟩
  exact lt_of_le_of_lt (CoordNode.meetLevel_le_right _ _) hj

/-- The actual E2^- nodes are closed under the coordinate-tree meet.
The proof uses only the embedding's exact aux-type meet preservation
and the fixed-prefix identity; no subtree completion is assumed. -/
theorem finiteAuxCandidate_meet
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (e : Ordered3Graph.Embedding A.toOrdered3Graph H.toOrdered3Graph)
    (haux : e.AuxTypeRespecting)
    (n : Nat) (hfix : ∀ k : Nat, k < n → e k = k)
    (x y : CoordNode)
    (hx : finiteAuxCandidate A H e n x)
    (hy : finiteAuxCandidate A H e n y) :
    finiteAuxCandidate A H e n (CoordNode.meet x y) := by
  rcases hx with ⟨i, B, hi, rfl⟩ |
      ⟨i, u₀, u₁, hni, hiu, hu, hum, rfl⟩
  · rcases hy with ⟨j, C, hj, rfl⟩ |
        ⟨j, v₀, v₁, hnj, hjv, hv, hvm, rfl⟩
    · exact Or.inl (auxMeet_prefix_left n i j B C hi)
    · exact Or.inl
        (auxMeet_prefix_left n i (e j) B
          (H.auxType (e j) (e v₀) (e v₁)) hi)
  · rcases hy with ⟨j, C, hj, rfl⟩ |
        ⟨j, v₀, v₁, hnj, hjv, hv, hvm, rfl⟩
    · exact Or.inl
        (auxMeet_prefix_right n (e i) j
          (H.auxType (e i) (e u₀) (e u₁)) C hj)
    · let k := min (min i j)
        (A.toOrdered3Graph.auxMeetLevel u₀ u₁ v₀ v₁)
      have hki : k ≤ i :=
        (min_le_left (min i j) _).trans (min_le_left i j)
      have hku : k ≤ u₀ := hki.trans hiu
      have hlev :
          CoordNode.meetLevel
            (.aux (e i) (H.auxType (e i) (e u₀) (e u₁)))
            (.aux (e j) (H.auxType (e j) (e v₀) (e v₁))) = e k :=
        A.selectedAux_meetLevel H e haux
          i j u₀ u₁ v₀ v₁ hiu hu hjv hv
      have hmeet :
          CoordNode.meet
            (.aux (e i) (H.auxType (e i) (e u₀) (e u₁)))
            (.aux (e j) (H.auxType (e j) (e v₀) (e v₁))) =
            .aux (e k) (H.auxType (e k) (e u₀) (e u₁)) := by
        calc
          CoordNode.meet
              (.aux (e i) (H.auxType (e i) (e u₀) (e u₁)))
              (.aux (e j) (H.auxType (e j) (e v₀) (e v₁))) =
              .aux (e k)
                ((H.auxType (e i) (e u₀) (e u₁)).truncate (e k)) := by
                  simp only [CoordNode.meet, CoordNode.truncate]
                  rw [hlev]
          _ = .aux (e k) (H.auxType (e k) (e u₀) (e u₁)) := by
              rw [H.auxType_truncate (u := e u₀) (v := e u₁)
                (e.strictMono.monotone hki)]
      by_cases hkn : k < n
      · left
        have heq : e k = k := hfix k hkn
        rw [heq] at hmeet
        exact ⟨k, H.auxType k (e u₀) (e u₁), hkn, hmeet⟩
      · right
        exact ⟨k, u₀, u₁, Nat.le_of_not_gt hkn,
          hku, hu, hum, hmeet⟩

end EnumNode
end ThreeUniformDiaries
