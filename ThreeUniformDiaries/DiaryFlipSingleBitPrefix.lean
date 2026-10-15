import ThreeUniformDiaries.DiaryFlipFiniteLevels

/-!
# The manuscript's one-bit flip word from the corrected role masks

Each source vertex is either a 1-split, a 2-split, a leaf or one
of the first three markers. The role-restricted pair of controls
in the existing prefix-tree API has at most ONE active bit at
any level. Its Boolean union is precisely the paper's one-bit
flip word p^A_B.

This proves a literal equivalence between the old two-coordinate
prefix nodes and the single-bit prefix nodes and produces a
finite depth-n candidate universe indexed by Fin n -> Bool,
rather than by two independent Boolean functions.

No statement about the cross-branch pre-diary completion is
deduced: the simplification concerns prefix encoding only.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RoleDiary
namespace FlipFamily

variable {A : Ordered3Graph Nat} {ι : Type*}

/-- The unique active split control at level m, or false at
markers and leaves: exactly the word used in the manuscript. -/
noncomputable def paperBit (T : FlipFamily A ι)
    (i : ι) (m : Nat) : Bool :=
  T.oneBit i m || T.twoBit i m

theorem oneBit_from_paperBit
    (T : FlipFamily A ι) (i : ι) (m : Nat) :
    T.oneBit i m =
      (if IsOneSplit A m then T.paperBit i m else false) := by
  classical
  by_cases hOne : IsOneSplit A m
  · have hNotTwo : ¬ IsTwoSplit A m := by
      intro ht
      exact ht.2.1 hOne.2.1
    simp [oneBit, twoBit, paperBit, hOne, hNotTwo]
  · simp [oneBit, paperBit, hOne]

theorem twoBit_from_paperBit
    (T : FlipFamily A ι) (i : ι) (m : Nat) :
    T.twoBit i m =
      (if IsTwoSplit A m then T.paperBit i m else false) := by
  classical
  by_cases hTwo : IsTwoSplit A m
  · have hNotOne : ¬ IsOneSplit A m := by
      intro ho
      exact hTwo.2.1 ho.2.1
    simp [oneBit, twoBit, paperBit, hTwo, hNotOne]
  · simp [twoBit, paperBit, hTwo]

theorem paperBit_false_before_three
    (T : FlipFamily A ι) (i : ι)
    (m : Nat) (hm : m < 3) :
    T.paperBit i m = false := by
  simp [paperBit,
    T.oneBit_false_before_three i m hm,
    T.twoBit_false_before_three i m hm]

/-- One finite binary word with a stored source level. -/
abbrev PaperFlipNode := Nat × (Nat → Bool)

noncomputable def paperNode
    (T : FlipFamily A ι) (i : ι) (n : Nat) :
    PaperFlipNode :=
  (n, fun m => if m < n then T.paperBit i m else false)

/-- Equal one-bit prefixes and equal two-control prefixes
are precisely the same equivalence relation on flip branches. -/
theorem paperNode_eq_iff_node_eq
    (T : FlipFamily A ι) (i j : ι) (n : Nat) :
    T.paperNode i n = T.paperNode j n ↔
      T.node i n = T.node j n := by
  constructor
  · intro h
    have hbits : ∀ m, m < n →
        T.paperBit i m = T.paperBit j m := by
      intro m hm
      have ht := congrFun (congrArg Prod.snd h) m
      simpa only [paperNode, if_pos hm] using ht
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext m
        by_cases hm : m < n
        · change (if m < n then T.oneBit i m else false) =
            (if m < n then T.oneBit j m else false)
          simp only [if_pos hm]
          rw [T.oneBit_from_paperBit i m,
              T.oneBit_from_paperBit j m, hbits m hm]
        · simp [node, hm]
      · funext m
        by_cases hm : m < n
        · change (if m < n then T.twoBit i m else false) =
            (if m < n then T.twoBit j m else false)
          simp only [if_pos hm]
          rw [T.twoBit_from_paperBit i m,
              T.twoBit_from_paperBit j m, hbits m hm]
        · simp [node, hm]
  · intro h
    apply Prod.ext
    · rfl
    · funext m
      by_cases hm : m < n
      · change (if m < n then T.paperBit i m else false) =
          (if m < n then T.paperBit j m else false)
        simp only [if_pos hm]
        have hOne := T.oneBit_eq_of_node_eq i j n m h hm
        have hTwo := T.twoBit_eq_of_node_eq i j n m h hm
        simp only [paperBit, hOne, hTwo]
      · simp [paperNode, hm]

/-- Role correctness forces the same marker prefix in the
original paper's single-control presentation as well. -/
theorem paperNodes_agree_through_markers
    (T : FlipFamily A ι) (i j : ι) (n : Nat) (hn : n ≤ 3) :
    T.paperNode i n = T.paperNode j n :=
  (T.paperNode_eq_iff_node_eq i j n).mpr
    (T.nodes_agree_through_markers i j n hn)

/-- Every paper prefix node is encoded by n actual Boolean values. -/
def paperNodeFromFiniteBits
    (n : Nat) (bits : Fin n → Bool) : PaperFlipNode :=
  (n, fun m => if hm : m < n then bits ⟨m, hm⟩ else false)

theorem paperNode_eq_finiteBits
    (T : FlipFamily A ι) (i : ι) (n : Nat) :
    T.paperNode i n =
      paperNodeFromFiniteBits n (fun k => T.paperBit i k.val) := by
  apply Prod.ext
  · rfl
  · funext m
    by_cases hm : m < n
    · simp [paperNode, paperNodeFromFiniteBits, hm]
    · simp [paperNode, paperNodeFromFiniteBits, hm]

/-- Sharp one-bit-per-level finite candidate universe. -/
noncomputable def paperLevelCandidates (n : Nat) :
    Finset PaperFlipNode := by
  classical
  exact (Finset.univ : Finset (Fin n → Bool)).image
    (paperNodeFromFiniteBits n)

theorem paperNode_mem_candidates
    (T : FlipFamily A ι) (i : ι) (n : Nat) :
    T.paperNode i n ∈ paperLevelCandidates n := by
  classical
  unfold paperLevelCandidates
  apply Finset.mem_image.mpr
  refine ⟨(fun k : Fin n => T.paperBit i k.val),
    Finset.mem_univ _, ?_⟩
  exact (T.paperNode_eq_finiteBits i n).symm

end FlipFamily
end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
