import ThreeUniformDiaries.InfiniteCanonicalSelectedAuxBits

/-!
# Exact selected pair bits of the actual infinite E1 canonical map

The concrete infinite singleton-type map inserts each new source pair
(i,j) at selected target coordinates (f(i),f(j)). The inserted E1
boundary parameter is itself the result of the lower auxiliary map,
which has already been shown to preserve each selected bit.

Earlier pairs persist by the concrete E1 selected restriction theorem.
This gives exact preservation of all increasing source pairs by the
constructed infinite map, without an abstract CanonicalMap hypothesis.

The E0 triple analogue will provide the induced hypergraph statement.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- The source pair (i,j) is inserted at precisely the selected
target coordinates (f(i),f(j)) when the source level j is added. -/
theorem infiniteOneCanonicalMap_newPair
    {S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₁ : OneNode (f 0)} {r₂ : AuxNode (f 0)}
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f)
    (j i : Nat) (hij : i < j) (a : OneNode (j + 1)) :
    (infiniteOneCanonicalMap h₁ h₂ (j + 1) a).val.pair
      (f i) (f j) = a.pair i j := by
  have hcone := infiniteOneCanonicalMap_succ
    h₁ h₂ j (a.truncate j) (a.boundaryAux j)
  rw [OneNode.succ_truncate_boundary] at hcone
  have hcut := hcone.2
  change CoordNode.one (f j + 1)
      ((infiniteOneCanonicalMap h₁ h₂ (j + 1) a).val.truncate
        (f j + 1)) =
    CoordNode.one (f j + 1)
      ((infiniteOneCanonicalMap h₁ h₂ j (a.truncate j)).val.succ
       (infiniteAuxCanonicalMap h₂ j (a.boundaryAux j)).val) at hcut
  have hbit := congrArg
    (fun x : CoordNode =>
      match x with
      | .one _ b => b.pair (f i) (f j)
      | _ => false) hcut
  have hpair :
      (infiniteOneCanonicalMap h₁ h₂ (j + 1) a).val.pair
        (f i) (f j) =
      (infiniteAuxCanonicalMap h₂ j (a.boundaryAux j)).val.bit
        (f i) := by
    simpa [CoordNode.truncate, OneNode.truncate,
      OneNode.succ, Nat.lt_succ_self] using hbit
  have haux :=
    infiniteAuxCanonicalMap_selectedBit h₂ hf j i hij
      (a.boundaryAux j)
  calc
    (infiniteOneCanonicalMap h₁ h₂ (j + 1) a).val.pair (f i) (f j) =
        (infiniteAuxCanonicalMap h₂ j (a.boundaryAux j)).val.bit (f i) :=
      hpair
    _ = (a.boundaryAux j).bit i := haux
    _ = a.pair i j := by simp [OneNode.boundaryAux, hij]

/-- Every increasing pair of original source coordinates is preserved
at the two corresponding selected target vertices. -/
theorem infiniteOneCanonicalMap_selectedPair
    {S₁ S₂ : Set CoordNode} {f : Nat → Nat}
    {r₁ : OneNode (f 0)} {r₂ : AuxNode (f 0)}
    (h₁ : InfiniteStrongPicture S₁ f (.one (f 0) r₁))
    (h₂ : InfiniteStrongPicture S₂ f (.aux (f 0) r₂))
    (hf : StrictMono f) :
    ∀ (N i j : Nat) (hij : i < j) (hjN : j < N) (a : OneNode N),
      (infiniteOneCanonicalMap h₁ h₂ N a).val.pair (f i) (f j) =
        a.pair i j := by
  intro N
  induction N with
  | zero =>
      intro i j hij hjN a
      omega
  | succ k ih =>
      intro i j hij hjN a
      by_cases hj : j = k
      · subst j
        exact infiniteOneCanonicalMap_newPair h₁ h₂ hf k i hij a
      · have hjk : j < k := by omega
        have hparent := infiniteOneCanonicalMap_parent h₁ h₂ k a
        have hb := congrArg
          (fun x : OneNode (f k) => x.pair (f i) (f j)) hparent
        have hfj : f j < f k := hf hjk
        have hprev :
            (infiniteOneCanonicalMap h₁ h₂ (k + 1) a).val.pair
              (f i) (f j) =
            (infiniteOneCanonicalMap h₁ h₂ k (a.truncate k)).val.pair
              (f i) (f j) := by
          simpa [OneNode.truncate, hfj] using hb
        calc
          (infiniteOneCanonicalMap h₁ h₂ (k + 1) a).val.pair (f i) (f j) =
              (infiniteOneCanonicalMap h₁ h₂ k (a.truncate k)).val.pair
                (f i) (f j) := hprev
          _ = (a.truncate k).pair i j :=
            ih i j hij hjk (a.truncate k)
          _ = a.pair i j := by simp [OneNode.truncate, hjk]

end CoordNode
end ThreeUniformDiaries
