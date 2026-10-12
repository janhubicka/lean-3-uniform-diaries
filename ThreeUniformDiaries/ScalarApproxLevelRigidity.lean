import Milliken.GeneralTree.SourceLevels
import ThreeUniformDiaries.RootGluedAmbientTree

/-!
# Finite scalar Milliken approximations determine their selected levels

An arbitrary general-tree finite approximation is stored as a node
carrier, with no chosen source-level map. Nonetheless, any two genuine
strong-tree realizers of the SAME height-n approximation have identical
first n selected ambient heights. This is essential for a geometric
ATR finite-code decoder to be independent of a chosen infinite realizer.

The proof uses actual nonempty source levels and strict monotonicity,
without a uniform bound on the degree of the type trees.
-/

namespace ThreeUniformDiaries
namespace ATRFiniteDecoder

open Milliken
open Milliken.GeneralTree

/-- Equality of the first n strong-tree source-level carriers fixes
all selected ambient heights below n. -/
theorem sourceLevels_eq_of_initialPart_eq
    {U : Milliken.AmbientTree}
    (S T : StrongSubtree U) (n : Nat)
    (hcarrier : S.initialPart n = T.initialPart n) :
    ∀ k : Nat, k < n → S.levels k = T.levels k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hk
      apply le_antisymm
      · obtain ⟨x, hx⟩ := T.sourceLevel_nonempty k
        have hT : x ∈ T.initialPart n :=
          ⟨hx.1, k, hk, hx.2⟩
        have hS : x ∈ S.initialPart n := by
          rw [hcarrier]
          exact hT
        obtain ⟨_, j, hjn, hlevel⟩ := hS
        have hkj : k ≤ j := by
          by_contra hnot
          have hjk : j < k := Nat.lt_of_not_ge hnot
          have hprev : S.levels j = T.levels j :=
            ih j hjk (lt_trans hjk hk)
          have hbad : T.levels j < T.levels k :=
            T.levels_strictMono hjk
          have hsame : T.levels j = T.levels k := by
            calc
              T.levels j = S.levels j := hprev.symm
              _ = U.level x := hlevel.symm
              _ = T.levels k := hx.2
          rw [hsame] at hbad
          exact (lt_irrefl _) hbad
        calc
          S.levels k ≤ S.levels j :=
            S.levels_strictMono.monotone hkj
          _ = U.level x := hlevel.symm
          _ = T.levels k := hx.2
      · obtain ⟨x, hx⟩ := S.sourceLevel_nonempty k
        have hS : x ∈ S.initialPart n :=
          ⟨hx.1, k, hk, hx.2⟩
        have hT : x ∈ T.initialPart n := by
          rw [← hcarrier]
          exact hS
        obtain ⟨_, j, hjn, hlevel⟩ := hT
        have hkj : k ≤ j := by
          by_contra hnot
          have hjk : j < k := Nat.lt_of_not_ge hnot
          have hprev : S.levels j = T.levels j :=
            ih j hjk (lt_trans hjk hk)
          have hbad : S.levels j < S.levels k :=
            S.levels_strictMono hjk
          have hsame : S.levels j = S.levels k := by
            calc
              S.levels j = T.levels j := hprev
              _ = U.level x := hlevel.symm
              _ = S.levels k := hx.2
          rw [hsame] at hbad
          exact (lt_irrefl _) hbad
        calc
          T.levels k ≤ T.levels j :=
            T.levels_strictMono.monotone hkj
          _ = U.level x := hlevel.symm
          _ = S.levels k := hx.2

/-- Equality of finite general-tree approximations implies equality
of the first n selected ambient heights of both actual realizers. -/
theorem sourceLevels_eq_of_approx_eq
    {U : Milliken.AmbientTree}
    (S T : StrongSubtree U) (n : Nat)
    (h : Milliken.GeneralTree.r n S = Milliken.GeneralTree.r n T) :
    ∀ k : Nat, k < n → S.levels k = T.levels k := by
  exact sourceLevels_eq_of_initialPart_eq S T n
    (congrArg Milliken.GeneralTree.FiniteApprox.carrier h)

end ATRFiniteDecoder
end ThreeUniformDiaries
