import ThreeUniformDiaries.DiaryFullRoleDefinition

/-!
# From relative orientation to a uniform global sign

The lower-bound proof needs to show that after stabilisation the
lexicographic orientation of *every* ordered leaf pair is either
preserved, or reversed uniformly. A single five-vertex gadget
proves only one local orientation equality; the missing step is
to compare arbitrary pairs in the same global system.

This module separates the elementary but essential logic from
that remaining geometric argument.

For any set of comparisons, equality of the source orientation
bits agrees with equality of the target bits on every pair of
comparisons if and only if the target signs are uniformly
identical to or uniformly opposite to the source signs. No
ordering assumption on the original external hypergraph map is
needed for this Boolean fact.

In particular, a proof that the diary's finite gadget relations
force relative orientation agreement for all ordered leaf pairs
will automatically yield the exact global preserve/reverse
dichotomy stated in the manuscript. The connectivity/amalgamation
step establishing that premise is *not* proved here.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Comparing the equality pattern of two arbitrary Prop-valued
orientations is equivalent to a single global preserve/reverse
choice, as soon as a reference comparison is supplied. -/
theorem relative_orientation_iff_uniform_sign
    {ι : Type*} (source target : ι → Prop) (reference : ι) :
    (∀ x y : ι,
      (source x ↔ source y) ↔ (target x ↔ target y)) ↔
      ((∀ x : ι, source x ↔ target x) ∨
       (∀ x : ι, source x ↔ ¬ target x)) := by
  classical
  constructor
  · intro hrel
    by_cases href : source reference ↔ target reference
    · left
      intro x
      have h := hrel x reference
      by_cases hsx : source x <;>
        by_cases htx : target x <;>
        by_cases hsr : source reference <;>
        by_cases htr : target reference <;> simp_all
    · right
      intro x
      have h := hrel x reference
      by_cases hsx : source x <;>
        by_cases htx : target x <;>
        by_cases hsr : source reference <;>
        by_cases htr : target reference <;> simp_all
  · intro huniform x y
    rcases huniform with hsame | hflip
    · have hx := hsame x
      have hy := hsame y
      by_cases hsx : source x <;>
        by_cases hsy : source y <;>
        by_cases htx : target x <;>
        by_cases hty : target y <;> simp_all
    · have hx := hflip x
      have hy := hflip y
      by_cases hsx : source x <;>
        by_cases hsy : source y <;>
        by_cases htx : target x <;>
        by_cases hty : target y <;> simp_all

/-- An actual ordered pair of leaves in a diary. This is only
the two leaf roles and numerical ordering, not an additional
orientation, split or pointed-envelope axiom. -/
structure OrderedLeafPair (H : Ordered3Graph Nat) where
  first : Nat
  second : Nat
  first_lt_second : first < second
  first_is_leaf : IsLeaf H first
  second_is_leaf : IsLeaf H second

/-- Relative lexicographic orientation agreement for ALL ordered
leaf pairs implies exactly the global preserve-or-reverse
dichotomy. The external target map is an arbitrary function
here; no relation preservation is smuggled into this statement.

The missing lower-bound argument must produce the quantified
relative-orientation hypothesis from the finite gadget and its
amalgamations. -/
theorem global_lex_sign_of_relative
    {H K : Ordered3Graph Nat}
    (φ : Nat → Nat)
    (reference : OrderedLeafPair H)
    (hrelative :
      ∀ p q : OrderedLeafPair H,
        (LexEarlier H p.first p.second ↔
         LexEarlier H q.first q.second) ↔
        (LexEarlier K (φ p.first) (φ p.second) ↔
         LexEarlier K (φ q.first) (φ q.second))) :
    (∀ p : OrderedLeafPair H,
       LexEarlier H p.first p.second ↔
         LexEarlier K (φ p.first) (φ p.second)) ∨
    (∀ p : OrderedLeafPair H,
       LexEarlier H p.first p.second ↔
         ¬ LexEarlier K (φ p.first) (φ p.second)) := by
  exact (relative_orientation_iff_uniform_sign
    (fun p : OrderedLeafPair H => LexEarlier H p.first p.second)
    (fun p : OrderedLeafPair H =>
      LexEarlier K (φ p.first) (φ p.second))
    reference).mp hrelative

/-- The converse checks that a single global reversal really is
harmless for pairwise relative orientation comparisons. -/
theorem relative_lex_of_global_sign
    {H K : Ordered3Graph Nat}
    (φ : Nat → Nat)
    (huniform :
      (∀ p : OrderedLeafPair H,
         LexEarlier H p.first p.second ↔
           LexEarlier K (φ p.first) (φ p.second)) ∨
      (∀ p : OrderedLeafPair H,
         LexEarlier H p.first p.second ↔
           ¬ LexEarlier K (φ p.first) (φ p.second))) :
    ∀ p q : OrderedLeafPair H,
      (LexEarlier H p.first p.second ↔
       LexEarlier H q.first q.second) ↔
      (LexEarlier K (φ p.first) (φ p.second) ↔
       LexEarlier K (φ q.first) (φ q.second)) := by
  intro p q
  rcases huniform with hsame | hflip
  · have hp := hsame p
    have hq := hsame q
    by_cases sp : LexEarlier H p.first p.second <;>
      by_cases sq : LexEarlier H q.first q.second <;>
      by_cases tp : LexEarlier K (φ p.first) (φ p.second) <;>
      by_cases tq : LexEarlier K (φ q.first) (φ q.second) <;> simp_all
  · have hp := hflip p
    have hq := hflip q
    by_cases sp : LexEarlier H p.first p.second <;>
      by_cases sq : LexEarlier H q.first q.second <;>
      by_cases tp : LexEarlier K (φ p.first) (φ p.second) <;>
      by_cases tq : LexEarlier K (φ q.first) (φ q.second) <;> simp_all

end DiaryLeafPriority
end ThreeUniformDiaries
