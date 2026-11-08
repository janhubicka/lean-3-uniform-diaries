import ThreeUniformDiaries.DiaryFiniteOrderedSumCarrier
import ThreeUniformDiaries.DiaryFiniteStageNoncompactness

/-!
# Track B: an explicit finite-order tower without a Nat-order colimit

A coherent tower of finite full diaries can have bounded, strictly
increasing, marker-fixing transition maps without those maps being
literal initial-segment inclusions. The existing leaf-at-3 rigidity
shows why rank-fixed full-diary extensions cannot be assumed.

Here is an independent SHARP ORDER-THEORETIC regression.
Take finite frames [0,n+4). At every successor use the SAME
verified marker-fixing, strictly increasing map
  rightBlockImage 4 :
    0 |-> 0, 1 |-> 1, 2 |-> 2,
    u |-> u+1 for u>=3.
It inserts a new nonmarker at rank 3 at every finite step.

Suppose all these finite embeddings had a coherent realization
by strictly increasing maps g_n into the SAME ordinal Nat.
Then the image g_n(3) of each newly inserted rank-3 position
forms an infinite STRICTLY DECREASING Nat sequence, impossible.

This is an explicit finite-LINEAR-ORDER tower with no Nat-realized
coherent colimit; it is NOT constructed from full diary V/E/S
structures and is NOT a counterexample to the actual verified
finite strong absorber tower or the countable flip property.

It rules out the invalid automatic inference:
  nested finite frames with bounded monotone transition maps
  => a countable Nat-enumerated target whose finite pictures
     realize all transition embeddings.
That conclusion needs an extra finite-predecessor/colimit
condition or a different target construction.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The concrete left-insertion map on finite enumerated frames
is already the checked two-block right-image map at n=4. It
fixes markers 0,1,2 and sends rank 3 to rank 4. -/
theorem rightBlockImage_four_marker_and_first_leaf :
    rightBlockImage 4 0 = 0 ∧
    rightBlockImage 4 1 = 1 ∧
    rightBlockImage 4 2 = 2 ∧
    rightBlockImage 4 3 = 4 := by
  simp [rightBlockImage]

/-- Every transition is a genuine bounded, strictly increasing
embedding [0,n+4) -> [0,n+5) of the finite LINEAR ORDERS.
No diary edge, role or numerical-meet structure is asserted. -/
theorem rightBlockImage_four_bounded_finiteOrderEmbedding
    (n : Nat) :
    StrictMono (rightBlockImage 4) ∧
    (∀ u : Nat, u < n+4 →
      rightBlockImage 4 u < n+5) := by
  refine ⟨rightBlockImage_strictMono 4 (by omega),?_⟩
  intro u hu
  by_cases hsmall : u < 3
  · simp [rightBlockImage,hsmall]
    omega
  · simp only [rightBlockImage,if_neg hsmall]
    omega

/-- The sequence of all source rank-3 images would be
strictly decreasing in any compatible order realization. -/
private theorem leftInsertTower_rank_three_descends
    (g : Nat → Nat → Nat)
    (hMono : ∀ n : Nat, StrictMono (g n))
    (hCompat : ∀ n u : Nat, u < n+4 →
      g n u = g (n+1) (rightBlockImage 4 u))
    (n : Nat) :
    g (n+1) 3 < g n 3 := by
  have hlt : g (n+1) 3 < g (n+1) 4 :=
    hMono (n+1) (by omega)
  have hEq : g n 3 = g (n+1) 4 := by
    simpa [rightBlockImage] using hCompat n 3 (by omega)
  exact hlt.trans_le (le_of_eq hEq.symm)

/-- There is NO coherent family of increasing Nat embeddings
for this finite order tower. The proof is an explicit direct
finite-injury/rank obstruction, not an appeal to any unproved
diary topological or Ramsey principle. -/
theorem no_Nat_order_colimit_of_repeated_left_insertion :
    ¬ ∃ g : Nat → Nat → Nat,
      (∀ n : Nat, StrictMono (g n)) ∧
      (∀ n u : Nat, u < n+4 →
        g n u = g (n+1) (rightBlockImage 4 u)) := by
  rintro ⟨g,hMono,hCompat⟩
  have hStep (n : Nat) :
      g (n+1) 3 < g n 3 :=
    leftInsertTower_rank_three_descends g hMono hCompat n
  have hRankBound : ∀ n : Nat, g n 3 + n ≤ g 0 3 := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
        have hDrop := hStep n
        omega
  have h := hRankBound (g 0 3 + 1)
  omega

end DiaryLeafPriority
end ThreeUniformDiaries
