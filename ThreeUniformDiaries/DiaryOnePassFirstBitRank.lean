import ThreeUniformDiaries.DiaryOnePassBinaryRankFacts

/-!
# First differing index of equal-length Boolean test words

For the source singleton code it is convenient to know where the
first differing test occurs, rather than synthesise an abstract
lexicographic order. This lemma uses actual indexed Boolean lists.
The previous arithmetic lemmas show that a zero at the first
different index makes the whole big-endian numeral smaller.

No assumptions about raw code injectivity, source diaries or output
diaries are made here.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- If two words have equal length, agree at all tests before q,
and differ false-versus-true at q, their actual binary numerals
are strictly ordered. -/
theorem onePass_binaryRank_lt_of_first_bit
    (xs ys : List Bool) (hlen : xs.length = ys.length)
    (q : Nat) (hq : q < xs.length)
    (hBefore : ∀ i : Nat, i < q → xs[i]? = ys[i]?)
    (hx : xs[q]? = some false) (hy : ys[q]? = some true) :
    binaryWordRank xs < binaryWordRank ys := by
  induction q generalizing xs ys with
  | zero =>
      cases xs with
      | nil => simp at hq
      | cons x xt =>
          cases ys with
          | nil => simp at hlen
          | cons y yt =>
              have hxf : x = false := by simpa using hx
              have hyt : y = true := by simpa using hy
              subst x
              subst y
              apply onePass_binaryRank_zero_lt_one
              simpa using hlen
  | succ q ih =>
      cases xs with
      | nil => simp at hq
      | cons x xt =>
          cases ys with
          | nil => simp at hlen
          | cons y yt =>
              have hxy : x = y := by
                have h := hBefore 0 (by omega)
                simpa using h
              subst y
              have hlenTail : xt.length = yt.length := by
                simpa using hlen
              have hqTail : q < xt.length := by
                simp only [List.length_cons] at hq
                omega
              have hBeforeTail : ∀ i : Nat, i < q →
                  xt[i]? = yt[i]? := by
                intro i hi
                have h := hBefore (i + 1) (by omega)
                simpa only [List.getElem?_cons_succ] using h
              have hxTail : xt[q]? = some false := by
                simpa only [List.getElem?_cons_succ] using hx
              have hyTail : yt[q]? = some true := by
                simpa only [List.getElem?_cons_succ] using hy
              have hLess : binaryWordRank xt < binaryWordRank yt :=
                ih xt yt hlenTail hqTail hBeforeTail hxTail hyTail
              rw [binaryWordRank_cons, binaryWordRank_cons, hlenTail]
              exact Nat.add_lt_add_left hLess _

/-- The reverse first-bit orientation reverses the strict
numerical inequality, without any auxiliary lex order relation. -/
theorem onePass_binaryRank_gt_of_first_bit
    (xs ys : List Bool) (hlen : xs.length = ys.length)
    (q : Nat) (hq : q < xs.length)
    (hBefore : ∀ i : Nat, i < q → xs[i]? = ys[i]?)
    (hx : xs[q]? = some true) (hy : ys[q]? = some false) :
    binaryWordRank ys < binaryWordRank xs := by
  apply onePass_binaryRank_lt_of_first_bit ys xs
    hlen.symm q (by omega)
  · intro i hi
    exact (hBefore i hi).symm
  · exact hy
  · exact hx

end DiaryLeafPriority
end ThreeUniformDiaries
