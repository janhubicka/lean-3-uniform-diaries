import ThreeUniformDiaries.GenericExtensionStep

/-!
# Track C: genuine generic one-step extension with a protected old E5 pattern

English proof and adversarial audit:
  janhubicka/3-uniform-diaries PR #299

Fix a FINITE set A of protected old source indices and an arbitrarily
prescribed positive/negative triple bit on each old pair in A.
Suppose an induced partial copy of G uses n selected target vertices,
all DISJOINT from A. The actual generic extension axiom can
SIMULTANEOUSLY force the new vertex's bit with every old pair
and its bit with every pair of selected copy vertices.

The two families of pair tests are disjoint, so there is no
compatibility condition between them. This exact one-step lemma
is the local combinatorial engine for building a whole induced
generic selfcopy inside a prescribed finite old E5-pattern fibre.

It is NOT yet the countable recursive construction, a full diary
relative successor, or countable diary unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- One genuine generic extension simultaneously realizes an arbitrary
complete Boolean pattern on pairs of a FINITE protected old set A
AND all required next-source-vertex hyperedges over the previously
embedded n vertices, provided the selected images avoid A.

The proposed previously selected images must be increasing (and
hence injective). The old protected vertices need not be ordered
against the selected images: disjointness ALONE makes the two
full-pair prescriptions compatible. All coordinates are below the
finite extension cut B. No role/S1/S2/marker conditions are used. -/
theorem GenericEnumerated3Graph.exists_extension_with_disjoint_old_pair_pattern
    (G : GenericEnumerated3Graph)
    (A : Finset Nat) (q : Nat → Nat → Bool)
    {n : Nat} (old : Fin n → Nat)
    (hMono : StrictMono old)
    (hDisjoint : ∀ i : Fin n, old i ∉ A)
    (B : Nat)
    (hAB : ∀ a : Nat, a ∈ A → a < B)
    (hOldB : ∀ i : Fin n, old i < B) :
    ∃ t : Nat, B ≤ t ∧
      (∀ a b : Nat, a ∈ A → b ∈ A → a < b →
        (G.graph.edge a b t ↔ q a b = true)) ∧
      (∀ i j : Fin n, i < j →
        (G.graph.edge (old i) (old j) t ↔
          G.graph.edge i.val j.val n)) := by
  classical
  let mask : Fin B → Fin B → Bool := fun x y =>
    decide (
      (x.val ∈ A ∧ y.val ∈ A ∧ q x.val y.val = true) ∨
      ∃ i j : Fin n,
        i < j ∧ old i = x.val ∧ old j = y.val ∧
        G.graph.edge i.val j.val n)
  obtain ⟨t, hBt, hMask⟩ := G.extension B mask
  refine ⟨t, hBt, ?_, ?_⟩
  · intro a b ha hb hab
    let aa : Fin B := ⟨a, hAB a ha⟩
    let bb : Fin B := ⟨b, hAB b hb⟩
    have hFin : aa < bb := hab
    have hBit : G.graph.edge a b t ↔ mask aa bb = true :=
      hMask aa bb hFin
    have hValue : mask aa bb = true ↔ q a b = true := by
      change
        decide ((a ∈ A ∧ b ∈ A ∧ q a b = true) ∨
          ∃ i j : Fin n,
            i < j ∧ old i = a ∧ old j = b ∧
            G.graph.edge i.val j.val n) = true ↔
        q a b = true
      simp only [decide_eq_true_eq]
      constructor
      · intro h
        rcases h with hOldPair | hNewPair
        · exact hOldPair.2.2
        · obtain ⟨i, j, _hij, hi, _hj, _hEdge⟩ := hNewPair
          have hNotA := hDisjoint i
          rw [hi] at hNotA
          exact False.elim (hNotA ha)
      · intro hq
        exact Or.inl ⟨ha, hb, hq⟩
    exact hBit.trans hValue
  · intro i j hij
    let ii : Fin B := ⟨old i, hOldB i⟩
    let jj : Fin B := ⟨old j, hOldB j⟩
    have hFin : ii < jj := hMono hij
    have hBit :
        G.graph.edge (old i) (old j) t ↔ mask ii jj = true :=
      hMask ii jj hFin
    have hValue :
        mask ii jj = true ↔ G.graph.edge i.val j.val n := by
      change
        decide ((old i ∈ A ∧ old j ∈ A ∧
            q (old i) (old j) = true) ∨
          ∃ x y : Fin n,
            x < y ∧ old x = old i ∧ old y = old j ∧
            G.graph.edge x.val y.val n) = true ↔
        G.graph.edge i.val j.val n
      simp only [decide_eq_true_eq]
      constructor
      · intro h
        rcases h with hOldPair | hNewPair
        · exact False.elim ((hDisjoint i) hOldPair.1)
        · obtain ⟨x, y, _hxy, hx, hy, hEdge⟩ := hNewPair
          have hxi : x = i := hMono.injective hx
          have hyj : y = j := hMono.injective hy
          simpa only [hxi, hyj] using hEdge
      · intro hEdge
        exact Or.inr ⟨i, j, hij, rfl, rfl, hEdge⟩
    exact hBit.trans hValue

end DiaryLeafPriority
end ThreeUniformDiaries
