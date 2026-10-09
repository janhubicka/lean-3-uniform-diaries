import ThreeUniformDiaries.FiniteEncoderRoots
import ThreeUniformDiaries.PrunedTypeTrees

/-!
# Roots and exact level sets of the finite E0/E1/E2 candidates

The no-fixed-prefix case was verified in FiniteEncoderRoots.
For a nonempty fixed prefix n, the original candidate sets contain
every ambient type-tree node at each level k<n. In particular the
unique level-zero node of each coordinate belongs to the picture
and is below all of its nodes.

In both cases the candidate sets occupy only levels e(i), i<m,
because e fixes each k<n. This supplies the level hypotheses of
the generic finite strong-completion theorem.
-/

namespace ThreeUniformDiaries
namespace EnumNode

private theorem oneZeroRoot_le {k : Nat} (B : OneNode k) :
    CoordNode.one 0 (OneNode.zero 0) ≤ CoordNode.one k B := by
  refine ⟨Nat.zero_le _, ?_⟩
  change CoordNode.one 0 (B.truncate 0) =
    CoordNode.one 0 (OneNode.zero 0)
  have hb : B.truncate 0 = OneNode.zero 0 := by
    apply OneNode.ext_pairs
    funext i j
    simp [OneNode.truncate, OneNode.zero]
  exact congrArg (CoordNode.one 0) hb

private theorem auxZeroRoot_le {k : Nat} (B : AuxNode k) :
    CoordNode.aux 0 (AuxNode.zero 0) ≤ CoordNode.aux k B := by
  refine ⟨Nat.zero_le _, ?_⟩
  change CoordNode.aux 0 (B.truncate 0) =
    CoordNode.aux 0 (AuxNode.zero 0)
  have hb : B.truncate 0 = AuxNode.zero 0 := by
    apply AuxNode.ext_bits
    funext i
    simp [AuxNode.truncate, AuxNode.zero]
  exact congrArg (CoordNode.aux 0) hb

private theorem enumZeroRoot_le {N k : Nat}
    (H : EnumNode N) (B : EnumNode k) :
    CoordNode.enum 0 (H.truncate 0) ≤ CoordNode.enum k B := by
  refine ⟨Nat.zero_le _, ?_⟩
  change CoordNode.enum 0 (B.truncate 0) =
    CoordNode.enum 0 (H.truncate 0)
  have hb : B.truncate 0 = H.truncate 0 := by
    apply EnumNode.ext_triples
    funext i j t
    simp [EnumNode.truncate]
  exact congrArg (CoordNode.enum 0) hb

/-- E1 has the whole first n levels, so for n>0 it has
the ambient 1-type root at zero. -/
theorem finiteOneCandidate_root_positive
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (e : Ordered3Graph.Embedding A.toOrdered3Graph H.toOrdered3Graph)
    (n : Nat) (hn : 0 < n) :
    ∃ r : CoordNode,
      finiteOneCandidate A H e n r ∧
      CoordNode.level r = 0 ∧
      ∀ x : CoordNode,
        finiteOneCandidate A H e n x → r ≤ x := by
  let r := CoordNode.one 0 (OneNode.zero 0)
  refine ⟨r, ?_, rfl, ?_⟩
  · left
    exact ⟨0, OneNode.zero 0, hn, rfl⟩
  · intro x hx
    rcases hx with ⟨k, B, hk, rfl⟩ |
        ⟨i, v, hni, hiv, hvm, rfl⟩
    · exact oneZeroRoot_le B
    · exact oneZeroRoot_le (H.oneType (e i) (e v))

/-- E2^- has the unique auxiliary root at zero when n>0. -/
theorem finiteAuxCandidate_root_positive
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (e : Ordered3Graph.Embedding A.toOrdered3Graph H.toOrdered3Graph)
    (n : Nat) (hn : 0 < n) :
    ∃ r : CoordNode,
      finiteAuxCandidate A H e n r ∧
      CoordNode.level r = 0 ∧
      ∀ x : CoordNode,
        finiteAuxCandidate A H e n x → r ≤ x := by
  let r := CoordNode.aux 0 (AuxNode.zero 0)
  refine ⟨r, ?_, rfl, ?_⟩
  · left
    exact ⟨0, AuxNode.zero 0, hn, rfl⟩
  · intro x hx
    rcases hx with ⟨k, B, hk, rfl⟩ |
        ⟨i, u₀, u₁, hni, hiu, hu, hum, rfl⟩
    · exact auxZeroRoot_le B
    · exact auxZeroRoot_le (H.auxType (e i) (e u₀) (e u₁))

/-- E0 likewise has the unique empty-enumeration root when n>0. -/
theorem finiteEnumCandidate_root_positive
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (e : Ordered3Graph.Embedding A.toOrdered3Graph H.toOrdered3Graph)
    (n : Nat) (hn : 0 < n) :
    ∃ r : CoordNode,
      finiteEnumCandidate H e n m r ∧
      CoordNode.level r = 0 ∧
      ∀ x : CoordNode,
        finiteEnumCandidate H e n m x → r ≤ x := by
  let r := CoordNode.enum 0 (H.truncate 0)
  refine ⟨r, ?_, rfl, ?_⟩
  · left
    exact ⟨0, H.truncate 0, hn, rfl⟩
  · intro x hx
    rcases hx with ⟨k, B, hk, rfl⟩ |
        ⟨i, hni, him, rfl⟩
    · exact enumZeroRoot_le H B
    · exact enumZeroRoot_le H (H.truncate (e i))

/-- All actual E0 candidates have a level among e[0,m). -/
theorem finiteEnumCandidate_levels
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (e : Ordered3Graph.Embedding A.toOrdered3Graph H.toOrdered3Graph)
    (n : Nat) (hnm : n ≤ m)
    (hfix : ∀ k < n, e k = k)
    (x : CoordNode) (hx : finiteEnumCandidate H e n m x) :
    ∃ i : Nat, i < m ∧ CoordNode.level x = e i := by
  rcases hx with ⟨k, B, hk, rfl⟩ | ⟨i, hni, him, rfl⟩
  · exact ⟨k, lt_of_lt_of_le hk hnm, by
      simpa only [CoordNode.level] using (hfix k hk).symm⟩
  · exact ⟨i, him, rfl⟩

/-- All actual E1 candidates have a level among e[0,m). -/
theorem finiteOneCandidate_levels
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (e : Ordered3Graph.Embedding A.toOrdered3Graph H.toOrdered3Graph)
    (n : Nat) (hnm : n ≤ m)
    (hfix : ∀ k < n, e k = k)
    (x : CoordNode) (hx : finiteOneCandidate A H e n x) :
    ∃ i : Nat, i < m ∧ CoordNode.level x = e i := by
  rcases hx with ⟨k, B, hk, rfl⟩ |
      ⟨i, v, hni, hiv, hvm, rfl⟩
  · exact ⟨k, lt_of_lt_of_le hk hnm, by
      simpa only [CoordNode.level] using (hfix k hk).symm⟩
  · exact ⟨i, lt_of_le_of_lt hiv hvm, rfl⟩

/-- All actual E2^- candidates have a level among e[0,m). -/
theorem finiteAuxCandidate_levels
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (e : Ordered3Graph.Embedding A.toOrdered3Graph H.toOrdered3Graph)
    (n : Nat) (hnm : n ≤ m)
    (hfix : ∀ k < n, e k = k)
    (x : CoordNode) (hx : finiteAuxCandidate A H e n x) :
    ∃ i : Nat, i < m ∧ CoordNode.level x = e i := by
  rcases hx with ⟨k, B, hk, rfl⟩ |
      ⟨i, u₀, u₁, hni, hiu, hu, hum, rfl⟩
  · exact ⟨k, lt_of_lt_of_le hk hnm, by
      simpa only [CoordNode.level] using (hfix k hk).symm⟩
  · exact ⟨i, lt_trans (lt_of_le_of_lt hiu hu) hum, rfl⟩

end EnumNode
end ThreeUniformDiaries
