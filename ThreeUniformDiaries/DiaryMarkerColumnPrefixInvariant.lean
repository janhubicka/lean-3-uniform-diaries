import ThreeUniformDiaries.DiaryLexColumnPrefixEarlier

/-!
# Track B: one chronological Devlin-marker column preserves old singleton prefixes

A raw union of diary branches has exactly one Devlin marker on pairs
lying in a branch, and neither marker on pairs belonging to no branch.
Fill the missing marker pair at one earlier leaf q using its current
LexEarlier comparison. If two later leaves had equal raw singleton
types through q+1, then the two raw marker-bit vectors at q agree:
the pairs are either both fixed with identical bits or both missing.
In the latter case the previously verified common-prefix LexEarlier
invariance forces both inserted bits to be identical.

This is only a ONE-COLUMN invariant. The full chronological recursion,
enriched flip quotient, mixed-meet transfer and target absorption
are independent obligations.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- No Devlin marker has yet been assigned to an ordered leaf pair. -/
def MissingDevlinPair (R : Ordered3Graph Nat) (q z : Nat) : Prop :=
  ¬ R.edge 1 q z ∧ ¬ R.edge 2 q z

/-- Fill the previously unassigned pairs with earlier leaf q.
The existing edges (including all within-branch marker edges)
remain fixed. The new pair gets marker 1 iff the OLD graph
satisfies LexEarlier q z, and marker 2 otherwise. -/
def fillMissingDevlinColumn (R : Ordered3Graph Nat) (q : Nat) :
    Ordered3Graph Nat where
  edge x y z :=
    R.edge x y z ∨
    (y = q ∧ q < z ∧ MissingDevlinPair R q z ∧
      ((x = 1 ∧ DiaryLeafPriority.LexEarlier R q z) ∨
       (x = 2 ∧ ¬ DiaryLeafPriority.LexEarlier R q z)))

/-- Both fixed/unassigned states agree whenever raw later-leaf
singleton profiles agree through the column at q. This checks
BOTH marker bits, not just marker 1. -/
theorem missingDevlinPair_iff_of_same_one_prefix
    (R : Ordered3Graph Nat) (q a b : Nat)
    (hq : 3 ≤ q)
    (hs : R.SameOneTypeBelow (q+1) a b) :
    MissingDevlinPair R q a ↔ MissingDevlinPair R q b := by
  have h1 : R.edge 1 q a ↔ R.edge 1 q b :=
    hs (by omega) (by omega)
  have h2 : R.edge 2 q a ↔ R.edge 2 q b :=
    hs (by omega) (by omega)
  simp [MissingDevlinPair, h1, h2]

/-- The decisive ONE-COLUMN transport: filling all missing Devlin
bits for earlier leaf q cannot split an equality of two later
singleton columns through q+1. Only an already proved general
LexEarlier common-prefix lemma is used. The old equality is NOT
assumed to reflect from the new graph, and no pre-diary axiom
is hidden here. -/
theorem fillMissingDevlinColumn_preserves_one_prefix
    (R : Ordered3Graph Nat) (q a b : Nat)
    (hq : 3 ≤ q)
    (hqa : q < a) (hqb : q < b)
    (hs : R.SameOneTypeBelow (q+1) a b) :
    (fillMissingDevlinColumn R q).SameOneTypeBelow (q+1) a b := by
  have hOld : R.SameOneTypeBelow q a b := by
    intro i j hij hjq
    exact hs hij (by omega)
  have hLex :
      DiaryLeafPriority.LexEarlier R q a ↔
        DiaryLeafPriority.LexEarlier R q b :=
    R.lexEarlier_eq_of_common_one_prefix
      q q a b hOld (le_refl q) hqa hqb
  have hMissing : MissingDevlinPair R q a ↔
      MissingDevlinPair R q b :=
    missingDevlinPair_iff_of_same_one_prefix R q a b hq hs
  intro x y hxy hy
  have hRaw : R.edge x y a ↔ R.edge x y b :=
    hs hxy hy
  change
    (R.edge x y a ∨
      (y = q ∧ q < a ∧ MissingDevlinPair R q a ∧
        ((x = 1 ∧ DiaryLeafPriority.LexEarlier R q a) ∨
         (x = 2 ∧ ¬ DiaryLeafPriority.LexEarlier R q a)))) ↔
    (R.edge x y b ∨
      (y = q ∧ q < b ∧ MissingDevlinPair R q b ∧
        ((x = 1 ∧ DiaryLeafPriority.LexEarlier R q b) ∨
         (x = 2 ∧ ¬ DiaryLeafPriority.LexEarlier R q b))))
  simp [hRaw, hMissing, hLex, hqa, hqb]

end Ordered3Graph
end ThreeUniformDiaries
