import ThreeUniformDiaries.DiaryFiniteOrderTowerColimitObstruction

/-!
# Track B: the finite-frame strength of the order-colimit obstruction

The preceding regression rules out coherent maps g_n : Nat → Nat
that are globally strictly increasing. Actual finite-frame order
realizations need strict monotonicity only on the frame [0,n+4).
This module closes that logical mismatch: even the WEAKER, exact
finite-frame monotonicity suffices for the same descent obstruction.

No diary structure, infinite carrier construction or countable
source flip property is asserted here.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Genuine local finite-order version of the left-insertion obstruction.
Each map g n is assumed strictly increasing only on the finite
source frame [0,n+4), with compatibility required on that frame.
No global StrictMono (g n) hypothesis is used. -/
theorem no_Nat_order_colimit_of_repeated_left_insertion_finiteFrame :
    ¬ ∃ g : Nat → Nat → Nat,
      (∀ n u v : Nat, u < v → v < n+4 → g n u < g n v) ∧
      (∀ n u : Nat, u < n+4 →
        g n u = g (n+1) (rightBlockImage 4 u)) := by
  rintro ⟨g,hFiniteMono,hCompat⟩
  have hStep (n : Nat) : g (n+1) 3 < g n 3 := by
    have hlt : g (n+1) 3 < g (n+1) 4 :=
      hFiniteMono (n+1) 3 4 (by omega) (by omega)
    have hEq : g n 3 = g (n+1) 4 := by
      simpa [rightBlockImage] using hCompat n 3 (by omega)
    exact hlt.trans_le (le_of_eq hEq.symm)
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
