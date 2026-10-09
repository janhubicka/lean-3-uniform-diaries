import ThreeUniformDiaries.FiniteLocalSelectedMeets
import ThreeUniformDiaries.FiniteAuxMeetClosure

/-!
# True meet closure of E1 and E2^- for finite-only embeddings

These are the same prescribed candidate sets as in manuscript Lemma
Aemb, now requiring only the genuine finite source embedding
hypotheses: induced edges below m and singleton/aux comparisons
among source vertices below m.

We do not assume the extension of the vertex map to artificial
source vertices >= m preserves any edges or type agreements.
-/

namespace ThreeUniformDiaries
namespace EnumNode

private theorem onePrefixMeetLeftFinite
    (n i j : Nat) (B : OneNode i) (C : OneNode j)
    (hi : i < n) :
    ∃ (k : Nat) (D : OneNode k),
      k < n ∧
        CoordNode.meet (.one i B) (.one j C) = .one k D := by
  let k := CoordNode.meetLevel (.one i B) (.one j C)
  refine ⟨k, B.truncate k, ?_, rfl⟩
  exact lt_of_le_of_lt (CoordNode.meetLevel_le_left _ _) hi

private theorem onePrefixMeetRightFinite
    (n i j : Nat) (B : OneNode i) (C : OneNode j)
    (hj : j < n) :
    ∃ (k : Nat) (D : OneNode k),
      k < n ∧
        CoordNode.meet (.one i B) (.one j C) = .one k D := by
  let k := CoordNode.meetLevel (.one i B) (.one j C)
  refine ⟨k, B.truncate k, ?_, rfl⟩
  exact lt_of_le_of_lt (CoordNode.meetLevel_le_right _ _) hj

/-- The concrete singleton candidate set is meet-closed under an
aux-type-respecting embedding of ONLY the finite m vertices. -/
theorem finiteOneCandidate_meet_of_finite
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (f : Nat → Nat)
    (hf : Ordered3Graph.FiniteAuxEmbedding
      A.toOrdered3Graph H.toOrdered3Graph f m)
    (n : Nat) (hfix : ∀ k < n, f k = k)
    (x y : CoordNode)
    (hx : finiteOneCandidate A H f n x)
    (hy : finiteOneCandidate A H f n y) :
    finiteOneCandidate A H f n (CoordNode.meet x y) := by
  rcases hx with ⟨i, B, hi, rfl⟩ |
      ⟨i, v, hni, hiv, hv, rfl⟩
  · rcases hy with ⟨j, C, hj, rfl⟩ |
        ⟨j, w, hnj, hjw, hw, rfl⟩
    · exact Or.inl (onePrefixMeetLeftFinite n i j B C hi)
    · exact Or.inl
        (onePrefixMeetLeftFinite n i (f j) B
          (H.oneType (f j) (f w)) hi)
  · rcases hy with ⟨j, C, hj, rfl⟩ |
        ⟨j, w, hnj, hjw, hw, rfl⟩
    · exact Or.inl
        (onePrefixMeetRightFinite n (f i) j
          (H.oneType (f i) (f v)) C hj)
    · let k := min (min i j)
        (A.toOrdered3Graph.oneMeetLevel v w)
      have hki : k ≤ i :=
        (min_le_left (min i j) _).trans (min_le_left i j)
      have hkv : k ≤ v := hki.trans hiv
      have hlev :
          CoordNode.meetLevel
            (.one (f i) (H.oneType (f i) (f v)))
            (.one (f j) (H.oneType (f j) (f w))) = f k :=
        A.selectedOne_meetLevel_of_finite H f hf
          i j v w hiv hjw hv hw
      have hmeet :
          CoordNode.meet
            (.one (f i) (H.oneType (f i) (f v)))
            (.one (f j) (H.oneType (f j) (f w))) =
            .one (f k) (H.oneType (f k) (f v)) := by
        calc
          CoordNode.meet
              (.one (f i) (H.oneType (f i) (f v)))
              (.one (f j) (H.oneType (f j) (f w))) =
              .one (f k)
                ((H.oneType (f i) (f v)).truncate (f k)) := by
                  simp only [CoordNode.meet, CoordNode.truncate]
                  rw [hlev]
          _ = .one (f k) (H.oneType (f k) (f v)) := by
              rw [H.oneType_truncate (u := f v)
                (hf.strictMono.monotone hki)]
      by_cases hkn : k < n
      · left
        have hfk : f k = k := hfix k hkn
        rw [hfk] at hmeet
        exact ⟨k, H.oneType k (f v), hkn, hmeet⟩
      · right
        exact ⟨k, v, Nat.le_of_not_gt hkn, hkv, hv, hmeet⟩

private theorem auxPrefixMeetLeftFinite
    (n i j : Nat) (B : AuxNode i) (C : AuxNode j)
    (hi : i < n) :
    ∃ (k : Nat) (D : AuxNode k),
      k < n ∧
        CoordNode.meet (.aux i B) (.aux j C) = .aux k D := by
  let k := CoordNode.meetLevel (.aux i B) (.aux j C)
  refine ⟨k, B.truncate k, ?_, rfl⟩
  exact lt_of_le_of_lt (CoordNode.meetLevel_le_left _ _) hi

private theorem auxPrefixMeetRightFinite
    (n i j : Nat) (B : AuxNode i) (C : AuxNode j)
    (hj : j < n) :
    ∃ (k : Nat) (D : AuxNode k),
      k < n ∧
        CoordNode.meet (.aux i B) (.aux j C) = .aux k D := by
  let k := CoordNode.meetLevel (.aux i B) (.aux j C)
  refine ⟨k, B.truncate k, ?_, rfl⟩
  exact lt_of_le_of_lt (CoordNode.meetLevel_le_right _ _) hj

/-- The actual E2^- candidate set is meet-closed under finite-only
selected-cut aux-type preservation, with no assumptions beyond m. -/
theorem finiteAuxCandidate_meet_of_finite
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (f : Nat → Nat)
    (hf : Ordered3Graph.FiniteAuxEmbedding
      A.toOrdered3Graph H.toOrdered3Graph f m)
    (n : Nat) (hfix : ∀ k < n, f k = k)
    (x y : CoordNode)
    (hx : finiteAuxCandidate A H f n x)
    (hy : finiteAuxCandidate A H f n y) :
    finiteAuxCandidate A H f n (CoordNode.meet x y) := by
  rcases hx with ⟨i, B, hi, rfl⟩ |
      ⟨i, u₀, u₁, hni, hiu, hu, hum, rfl⟩
  · rcases hy with ⟨j, C, hj, rfl⟩ |
        ⟨j, v₀, v₁, hnj, hjv, hv, hvm, rfl⟩
    · exact Or.inl (auxPrefixMeetLeftFinite n i j B C hi)
    · exact Or.inl
        (auxPrefixMeetLeftFinite n i (f j) B
          (H.auxType (f j) (f v₀) (f v₁)) hi)
  · rcases hy with ⟨j, C, hj, rfl⟩ |
        ⟨j, v₀, v₁, hnj, hjv, hv, hvm, rfl⟩
    · exact Or.inl
        (auxPrefixMeetRightFinite n (f i) j
          (H.auxType (f i) (f u₀) (f u₁)) C hj)
    · let k := min (min i j)
        (A.toOrdered3Graph.auxMeetLevel u₀ u₁ v₀ v₁)
      have hki : k ≤ i :=
        (min_le_left (min i j) _).trans (min_le_left i j)
      have hku : k ≤ u₀ := hki.trans hiu
      have hlev :
          CoordNode.meetLevel
            (.aux (f i) (H.auxType (f i) (f u₀) (f u₁)))
            (.aux (f j) (H.auxType (f j) (f v₀) (f v₁))) = f k :=
        A.selectedAux_meetLevel_of_finite H f hf
          i j u₀ u₁ v₀ v₁ hiu hu hum hjv hv hvm
      have hmeet :
          CoordNode.meet
            (.aux (f i) (H.auxType (f i) (f u₀) (f u₁)))
            (.aux (f j) (H.auxType (f j) (f v₀) (f v₁))) =
            .aux (f k) (H.auxType (f k) (f u₀) (f u₁)) := by
        calc
          CoordNode.meet
              (.aux (f i) (H.auxType (f i) (f u₀) (f u₁)))
              (.aux (f j) (H.auxType (f j) (f v₀) (f v₁))) =
              .aux (f k)
                ((H.auxType (f i) (f u₀) (f u₁)).truncate (f k)) := by
                  simp only [CoordNode.meet, CoordNode.truncate]
                  rw [hlev]
          _ = .aux (f k) (H.auxType (f k) (f u₀) (f u₁)) := by
              rw [H.auxType_truncate (u := f u₀) (v := f u₁)
                (hf.strictMono.monotone hki)]
      by_cases hkn : k < n
      · left
        have hfk : f k = k := hfix k hkn
        rw [hfk] at hmeet
        exact ⟨k, H.auxType k (f u₀) (f u₁), hkn, hmeet⟩
      · right
        exact ⟨k, u₀, u₁, Nat.le_of_not_gt hkn,
          hku, hu, hum, hmeet⟩

end EnumNode
end ThreeUniformDiaries
