import ThreeUniformDiaries.DiaryOnePassGermSignatures

/-!
# Lexicographic singleton-child scheduling for one-pass completion

At each original cut m, the finite source singleton code s_(m+1)
records increasing tests in lexicographic sequence: first their
second coordinate b, then their first coordinate a<b. All normal
children in a fixed s_m parent therefore have finite equal-length
binary words. The smaller child is the child with the smaller
binary numerical value; terminal child is strictly smaller than
every normal child, as it is a proper-prefix type.

We provide the actual finite word and numerical rank, a canonical
least-by-rank default, and insertion sorting in DECREASING rank.
These definitions make the event order explicit; the separate global
transport/V3 theorem is not claimed in this module.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The valid increasing singleton-test coordinates (a,b),
ordered first by b and then by a, as in the paper's s_m. -/
def oneCodeBitWord (m : Nat) (c : OneCodeSpace m) : List Bool :=
  (List.finRange m).flatMap (fun b : Fin m =>
    (List.finRange b.val).map (fun a : Fin b.val =>
      c ⟨a.val, lt_trans a.isLt b.isLt⟩ b))

/-- Interpret a finite 0/1 word as a big-endian binary numeral;
for equal-length words this preserves their lexicographic order. -/
def oneCodeBinaryRank (m : Nat) (c : OneCodeSpace m) : Nat :=
  (oneCodeBitWord m c).foldl
    (fun value bit => 2 * value + (if bit then 1 else 0)) 0

/-- Distinguish the terminal child from the next-cut normal
children. Rank zero is reserved for terminal, and every normal
child has rank at least one. -/
def oneGermBinaryRank (m : Nat) (g : OneGermSpace m) : Nat :=
  match g.2 with
  | none => 0
  | some c => oneCodeBinaryRank (m + 1) c + 1

theorem terminal_oneGerm_rank_zero (H : Ordered3Graph Nat) (m : Nat) :
    oneGermBinaryRank m (oneGermCode H m m) = 0 := by
  simp [oneGermBinaryRank, oneGermCode]

theorem normal_oneGerm_rank_pos
    (H : Ordered3Graph Nat) (m u : Nat) (hu : u ≠ m) :
    0 < oneGermBinaryRank m (oneGermCode H m u) := by
  simp [oneGermBinaryRank, oneGermCode, hu]

/-- Keep the smallest-ranked realised child seen so far. -/
def chooseSmallerOneGerm
    (m : Nat) (best : Option (OneGermSpace m))
    (g : OneGermSpace m) : Option (OneGermSpace m) :=
  match best with
  | none => some g
  | some h => if oneGermBinaryRank m g < oneGermBinaryRank m h
      then some g else some h

/-- For a nonempty finite parent fibre, the least ranked child
is used as the all-zero default when there is no terminal child. -/
def leastOneGermByRank
    (m : Nat) (children : List (OneGermSpace m)) :
    Option (OneGermSpace m) :=
  children.foldl (chooseSmallerOneGerm m) none

/-- Insert an event child into a list in decreasing binary-word
rank order. This is a direct finite insertion sort, independent
of any implementation-specific ordering on finite code spaces. -/
def insertOneGermDescending
    (m : Nat) (g : OneGermSpace m) :
    List (OneGermSpace m) → List (OneGermSpace m)
  | [] => [g]
  | h :: tail =>
      if oneGermBinaryRank m g ≥ oneGermBinaryRank m h then
        g :: h :: tail
      else
        h :: insertOneGermDescending m g tail

def sortOneGermsDescending
    (m : Nat) (children : List (OneGermSpace m)) :
    List (OneGermSpace m) :=
  children.foldr (insertOneGermDescending m) []

/-- Insertion sort never loses or duplicates an event position. -/
theorem insertOneGermDescending_length
    (m : Nat) (g : OneGermSpace m)
    (children : List (OneGermSpace m)) :
    (insertOneGermDescending m g children).length =
      children.length + 1 := by
  induction children with
  | nil => simp [insertOneGermDescending]
  | cons h tail ih =>
    by_cases hr : oneGermBinaryRank m g ≥ oneGermBinaryRank m h
    · simp [insertOneGermDescending, hr]
    · simp [insertOneGermDescending, hr, ih]

theorem sortOneGermsDescending_length
    (m : Nat) (children : List (OneGermSpace m)) :
    (sortOneGermsDescending m children).length =
      children.length := by
  induction children with
  | nil => rfl
  | cons g tail ih =>
    change (insertOneGermDescending m g
      (sortOneGermsDescending m tail)).length = (g :: tail).length
    rw [insertOneGermDescending_length, ih]
    rfl

end DiaryLeafPriority
end ThreeUniformDiaries
