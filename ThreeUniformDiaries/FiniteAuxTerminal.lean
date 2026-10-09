import ThreeUniformDiaries.FiniteAuxMeetClosure
import ThreeUniformDiaries.TreeMeetTerminalExtension

/-!
# The terminal auxiliary node in the finite strong-tree encoder

If m > 1 and n < m, the selected auxiliary-type set E2^- has
selected levels through e(m-2), but not e(m-1). We exhibit a node p
at the last old level, extend it to a canonical auxiliary node z at
level e(m-1), and prove the enlarged set remains meet-closed.

The case m = 1 has no lower selected pair and can be handled by a
singleton auxiliary node. The case n = m already contains its final
level in the prescribed initial prefix.
-/

namespace ThreeUniformDiaries
namespace EnumNode

/-- Two auxiliary coordinate nodes always share their unique
level-zero predecessor. -/
private theorem auxNodes_common
    {i j : Nat} (B : AuxNode i) (C : AuxNode j) :
    ∃ c : CoordNode,
      c ≤ CoordNode.aux i B ∧ c ≤ CoordNode.aux j C := by
  have h0 : B.truncate 0 = C.truncate 0 := by
    apply AuxNode.ext_bits
    funext k
    simp [AuxNode.truncate]
  refine ⟨CoordNode.aux 0 (B.truncate 0), ?_, ?_⟩
  · exact ⟨Nat.zero_le i, rfl⟩
  · refine ⟨Nat.zero_le j, ?_⟩
    change C.truncate 0 = B.truncate 0
    exact h0.symm

/-- For m >= 2 and a proper fixed prefix, there is a terminal
auxiliary node at e(m-1) extending the last occupied E2^- level.
Adjoining it preserves the actual coordinate-tree meet operation. -/
theorem finiteAuxCandidate_terminal
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (e : Ordered3Graph.Embedding A.toOrdered3Graph H.toOrdered3Graph)
    (haux : e.AuxTypeRespecting)
    (n : Nat) (hn : n < m) (hm : 1 < m)
    (hfix : ∀ k : Nat, k < n → e k = k) :
    ∃ p z : CoordNode,
      finiteAuxCandidate A H e n p ∧
      p ≤ z ∧
      CoordNode.level z = e (m - 1) ∧
      CoordNode.MeetClosed
        (Set.insert z {x | finiteAuxCandidate A H e n x}) := by
  let p : CoordNode :=
    .aux (e (m - 2))
      (H.auxType (e (m - 2)) (e (m - 2)) (e (m - 1)))
  let z : CoordNode :=
    .aux (e (m - 1))
      (H.auxType (e (m - 1)) (e (m - 2)) (e (m - 1)))
  let S : Set CoordNode := {x | finiteAuxCandidate A H e n x}
  have hp : p ∈ S := by
    change finiteAuxCandidate A H e n p
    by_cases hsel : n ≤ m - 2
    · right
      exact ⟨m - 2, m - 2, m - 1, hsel,
        le_rfl, by omega, by omega, rfl⟩
    · left
      have hk : m - 2 < n := Nat.lt_of_not_ge hsel
      have heq : e (m - 2) = m - 2 := hfix (m - 2) hk
      refine ⟨m - 2, H.auxType (m - 2)
        (e (m - 2)) (e (m - 1)), hk, ?_⟩
      change p = CoordNode.aux (m - 2)
        (H.auxType (m - 2) (e (m - 2)) (e (m - 1)))
      simp only [p, heq]
  have hcut : e (m - 2) ≤ e (m - 1) :=
    e.strictMono.monotone (by omega)
  have hpz : p ≤ z := by
    refine ⟨by simpa only [CoordNode.level, p, z] using hcut, ?_⟩
    change CoordNode.aux (e (m - 2))
        ((H.auxType (e (m - 1)) (e (m - 2)) (e (m - 1)))
          .truncate (e (m - 2))) =
      CoordNode.aux (e (m - 2))
        (H.auxType (e (m - 2)) (e (m - 2)) (e (m - 1)))
    rw [H.auxType_truncate (u := e (m - 2))
      (v := e (m - 1)) hcut]
  have hS : CoordNode.MeetClosed S := by
    intro x y hx hy
    exact A.finiteAuxCandidate_meet H e haux n hfix x y hx hy
  have hmax : ∀ x ∈ S, CoordNode.level x ≤ CoordNode.level p := by
    intro x hx
    change finiteAuxCandidate A H e n x at hx
    rcases hx with ⟨k, B, hk, rfl⟩ |
        ⟨i, u₀, u₁, hni, hiu, hu, hum, rfl⟩
    · have hkm : k ≤ m - 2 := by omega
      change k ≤ e (m - 2)
      calc
        k = e k := (hfix k hk).symm
        _ ≤ e (m - 2) := e.strictMono.monotone hkm
    · have him : i ≤ m - 2 := by omega
      change e i ≤ e (m - 2)
      exact e.strictMono.monotone him
  have hcommon :
      ∀ x ∈ S, ∃ c : CoordNode, c ≤ p ∧ c ≤ x := by
    intro x hx
    change finiteAuxCandidate A H e n x at hx
    rcases hx with ⟨k, B, hk, rfl⟩ |
        ⟨i, u₀, u₁, hni, hiu, hu, hum, rfl⟩
    · exact auxNodes_common
        (H.auxType (e (m - 2)) (e (m - 2)) (e (m - 1))) B
    · exact auxNodes_common
        (H.auxType (e (m - 2)) (e (m - 2)) (e (m - 1)))
        (H.auxType (e i) (e u₀) (e u₁))
  refine ⟨p, z, hp, hpz, rfl, ?_⟩
  exact CoordNode.meetClosed_insertAbove S hS p z
    hp hpz hmax hcommon

end EnumNode
end ThreeUniformDiaries
