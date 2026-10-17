import ThreeUniformDiaries.DiaryOnePassLexRanking

/-!
# General arithmetic of finite binary test words

The pre-diary construction encodes each finite singleton type in
big-endian binary order. The key orientation fact is entirely
finite: words of equal length are ordered by their first different
bit. The following elementary arithmetic lemmas make this true
for the *actual foldl numeral* used by oneCodeBinaryRank.

They do not claim injectivity on arbitrary raw OneCodeSpace:
oneCodeBitWord deliberately omits invalid coordinates a >= b.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

private def rankStep (n : Nat) (b : Bool) : Nat :=
  2 * n + if b then 1 else 0

private def binaryWordRank (xs : List Bool) : Nat :=
  xs.foldl rankStep 0

private theorem binaryWordRank_acc (xs : List Bool) (n : Nat) :
    xs.foldl rankStep n = 2 ^ xs.length * n + binaryWordRank xs := by
  induction xs generalizing n with
  | nil =>
      simp [binaryWordRank]
  | cons b xs ih =>
      have ha := ih (rankStep n b)
      have hb := ih (rankStep 0 b)
      change xs.foldl rankStep (rankStep n b) =
        2 ^ (xs.length + 1) * n + xs.foldl rankStep (rankStep 0 b)
      rw [ha, hb]
      cases b <;> simp [rankStep, pow_succ] <;> ring

private theorem binaryWordRank_cons (b : Bool) (xs : List Bool) :
    binaryWordRank (b :: xs) =
      (if b then 1 else 0) * 2 ^ xs.length + binaryWordRank xs := by
  change xs.foldl rankStep (rankStep 0 b) = _
  rw [binaryWordRank_acc]
  cases b <;> simp [rankStep] <;> ring

/-- Numeral of an appended finite word: suffix length sets the
binary positional weight of the common prefix. -/
theorem onePass_binaryRank_append (xs ys : List Bool) :
    binaryWordRank (xs ++ ys) =
      2 ^ ys.length * binaryWordRank xs + binaryWordRank ys := by
  simp only [binaryWordRank, List.foldl_append]
  rw [binaryWordRank_acc]

/-- Any binary word numeral fits strictly below 2 to its length. -/
theorem onePass_binaryRank_lt_pow (xs : List Bool) :
    binaryWordRank xs < 2 ^ xs.length := by
  induction xs with
  | nil =>
      simp [binaryWordRank]
  | cons b xs ih =>
      rw [binaryWordRank_cons]
      simp only [List.length_cons, pow_succ]
      cases b <;> simp <;> omega

/-- A zero leading bit is strictly smaller than a one leading bit,
regardless of the tails, as long as they have the same length. -/
theorem onePass_binaryRank_zero_lt_one (xs ys : List Bool)
    (hlen : xs.length = ys.length) :
    binaryWordRank (false :: xs) <
      binaryWordRank (true :: ys) := by
  rw [binaryWordRank_cons, binaryWordRank_cons]
  simp only [Bool.false_eq_true, reduceIte, zero_mul, zero_add, one_mul]
  have hbound := onePass_binaryRank_lt_pow xs
  rw [hlen] at hbound
  omega

/-- A common prefix never alters the direction of the first
different bit in equal-length Boolean words. -/
theorem onePass_binaryRank_prefix_zero_lt_one
    (prefix xs ys : List Bool) (hlen : xs.length = ys.length) :
    binaryWordRank (prefix ++ false :: xs) <
      binaryWordRank (prefix ++ true :: ys) := by
  rw [onePass_binaryRank_append, onePass_binaryRank_append]
  have hsame : (false :: xs).length = (true :: ys).length := by
    simpa using hlen
  rw [hsame]
  have hlt := onePass_binaryRank_zero_lt_one xs ys hlen
  omega

/-- The existing singleton-code rank is literally the binary
word numeral above, not a surrogate lex predicate. -/
theorem oneCodeBinaryRank_eq_word
    (m : Nat) (c : OneCodeSpace m) :
    oneCodeBinaryRank m c = binaryWordRank (oneCodeBitWord m c) := rfl

end DiaryLeafPriority
end ThreeUniformDiaries
