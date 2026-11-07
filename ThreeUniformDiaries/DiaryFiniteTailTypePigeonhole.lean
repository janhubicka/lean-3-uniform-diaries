import ThreeUniformDiaries.DiaryFiniteTailUnaryTypeCodes

/-!
# Some finite mixed unary-type cone recurs cofinally in any sequence

A finite colouring of Nat has a colour that occurs at arbitrarily
large input indices. Apply this to the COMPLETE finite mixed
singleton-type code below numerical cut B. For any prescribed map
F : Nat -> Nat, one code of tail vertices F(n) recurs at arbitrarily
large n; the corresponding target vertices have the SAME singleton
type below B (including every mixed edge and nonedge test).

If F is injective, these are infinitely many DISTINCT target
vertices. Even so, the recurrent code need not be the particular
one required by a fixed old support image; and the recurrent
class need not contain a universal induced leaf hypergraph copy.

This theorem is a finite pigeonhole consequence, NOT relative
tail realization or countable diary unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- One colour of any finite colouring of the natural numbers
occurs at arbitrarily late input indices. The finite family
of allowable colours is supplied explicitly by W. -/
theorem finite_colouring_has_cofinal_fiber
    {α : Type*} [DecidableEq α]
    (W : Finset α) (c : Nat → α)
    (hCover : ∀ n : Nat, c n ∈ W) :
    ∃ p : α, p ∈ W ∧
      ∀ N : Nat, ∃ n : Nat, N ≤ n ∧ c n = p := by
  classical
  by_contra hNone
  have hBad (p : α) (hp : p ∈ W) :
      ∃ N : Nat, ∀ n : Nat, N ≤ n → c n ≠ p := by
    by_contra hNo
    push_neg at hNo
    exact hNone ⟨p,hp,hNo⟩
  let failAt : α → Nat := fun p =>
    if hp : p ∈ W then Classical.choose (hBad p hp) else 0
  let N : Nat := W.sup failAt
  have hN : c N ∈ W := hCover N
  have hBound : failAt (c N) ≤ N :=
    Finset.le_sup (f := failAt) hN
  have hFail :
      ∀ n : Nat, failAt (c N) ≤ n → c n ≠ c N := by
    simpa only [failAt, dif_pos hN] using
      (Classical.choose_spec (hBad (c N) hN))
  exact (hFail N hBound) rfl

/-- Every prescribed sequence has an arbitrarily recurrent FULL
mixed singleton type below the selected finite cut B. The colour
is not fixed in advance and is not guaranteed to be a safe
relative one-step type for any prescribed stage. -/
theorem exists_cofinal_tailOneTypeCode
    (K : Ordered3Graph Nat) (B : Nat) (F : Nat → Nat) :
    ∃ p : Finset (Nat × Nat),
      p ∈ (tailOneTypeTests B).powerset ∧
      ∀ N : Nat, ∃ n : Nat, N ≤ n ∧
        tailOneTypeCode K B (F n) = p := by
  exact finite_colouring_has_cofinal_fiber
    (tailOneTypeTests B).powerset
    (fun n => tailOneTypeCode K B (F n))
    (fun n => tailOneTypeCode_mem_finite_powerset K B (F n))


/-- An injection of Nat into Nat eventually escapes every bounded
target interval: each of its finitely many possible small output
values has at most one preimage. No monotonicity is assumed. -/
theorem injective_nat_eventually_above
    (F : Nat → Nat) (hInj : Function.Injective F)
    (M : Nat) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n → M < F n := by
  classical
  let pre (t : Nat) : Nat :=
    if ht : ∃ n : Nat, F n = t then Classical.choose ht else 0
  let N : Nat := ((Finset.range (M + 1)).sup pre) + 1
  refine ⟨N,?_⟩
  intro n hn
  by_contra hNot
  have hFBound : F n ≤ M := by omega
  have hMem : F n ∈ Finset.range (M + 1) :=
    Finset.mem_range.mpr (by omega)
  have hExists : ∃ k : Nat, F k = F n := ⟨n,rfl⟩
  have hPreEq : F (pre (F n)) = F n := by
    simpa only [pre,dif_pos hExists] using
      (Classical.choose_spec hExists)
  have hEq : pre (F n) = n := hInj hPreEq
  have hSup : pre (F n) ≤ (Finset.range (M + 1)).sup pre :=
    Finset.le_sup (f := pre) hMem
  dsimp [N] at hn
  omega

/-- For an INJECTIVE prescribed outer leaf map, SOME complete mixed
singleton type cone contains arbitrarily large target positions.
The cone is chosen after seeing the map F; it is NOT guaranteed
to be the one required by any fixed old diary stage. -/
theorem exists_numerically_unbounded_tailOneTypeCode_fiber
    (K : Ordered3Graph Nat) (B : Nat)
    (F : Nat → Nat) (hInj : Function.Injective F) :
    ∃ p : Finset (Nat × Nat),
      p ∈ (tailOneTypeTests B).powerset ∧
      ∀ M : Nat, ∃ n : Nat, M < F n ∧
        tailOneTypeCode K B (F n) = p := by
  obtain ⟨p,hp,hCofinal⟩ :=
    exists_cofinal_tailOneTypeCode K B F
  refine ⟨p,hp,?_⟩
  intro M
  obtain ⟨N,hEscape⟩ := injective_nat_eventually_above F hInj M
  obtain ⟨n,hn,hCode⟩ := hCofinal N
  exact ⟨n,hEscape n hn,hCode⟩


end DiaryLeafPriority
end ThreeUniformDiaries
