import ThreeUniformDiaries.InfiniteCanonicalAuxOneRestriction

/-!
# Exact selected auxiliary bits in a concrete infinite canonical map

The actual infinite E2 canonical recursion inserts the source bit
at every selected target vertex f(i). Subsequent steps preserve
the earlier selected bits by selected-level truncation.

Consequently, for any source auxiliary type a on level N and every
i<N, the bit of its canonical target image at f(i) is literally
a.bit i. This is a checked hypergraph/type-compatibility property of
the constructed infinite map, NOT a postulated CanonicalMap field.

It is the E2 base of the simultaneous E1-pair and E0-triple
compatibility proof for the manuscript's infinite canonical-map lemma.
-/

namespace ThreeUniformDiaries
namespace CoordNode

/-- Each new source auxiliary bit is placed at its exactly selected
ambient target vertex, even across arbitrarily skipped target levels. -/
theorem infiniteAuxCanonicalMap_newBit
    {S : Set CoordNode} {f : Nat → Nat}
    {r : AuxNode (f 0)}
    (hS : InfiniteStrongPicture S f (.aux (f 0) r))
    (j : Nat) (a : AuxNode (j + 1)) :
    (infiniteAuxCanonicalMap hS (j + 1) a).val.bit (f j) =
      a.bit j := by
  have hcone :=
    infiniteAuxCanonicalMap_succ hS j (a.truncate j) (a.bit j)
  rw [AuxNode.succ_truncate_new] at hcone
  have hcut := hcone.2
  change CoordNode.aux (f j + 1)
      ((infiniteAuxCanonicalMap hS (j + 1) a).val.truncate
        (f j + 1)) =
    CoordNode.aux (f j + 1)
      ((infiniteAuxCanonicalMap hS j (a.truncate j)).val.succ
        (a.bit j)) at hcut
  have hbit := congrArg
    (fun x : CoordNode =>
      match x with
      | .aux _ b => b.bit (f j)
      | _ => false) hcut
  simpa [CoordNode.truncate, AuxNode.truncate,
    AuxNode.succ, Nat.lt_succ_self] using hbit

/-- All selected auxiliary bits are preserved, not merely the last
one. This also proves the earlier images survive skipped intervals. -/
theorem infiniteAuxCanonicalMap_selectedBit
    {S : Set CoordNode} {f : Nat → Nat}
    {r : AuxNode (f 0)}
    (hS : InfiniteStrongPicture S f (.aux (f 0) r))
    (hf : StrictMono f) :
    ∀ (N i : Nat) (hi : i < N) (a : AuxNode N),
      (infiniteAuxCanonicalMap hS N a).val.bit (f i) =
        a.bit i := by
  intro N
  induction N with
  | zero =>
      intro i hi a
      omega
  | succ j ih =>
      intro i hi a
      by_cases hlast : i = j
      · subst i
        exact infiniteAuxCanonicalMap_newBit hS j a
      · have hij : i < j := by omega
        have hparent :=
          infiniteAuxCanonicalMap_parent hS j a
        have hb := congrArg
          (fun x : AuxNode (f j) => x.bit (f i)) hparent
        have hfi : f i < f j := hf hij
        have hprev :
            (infiniteAuxCanonicalMap hS (j + 1) a).val.bit (f i) =
            (infiniteAuxCanonicalMap hS j (a.truncate j)).val.bit (f i) := by
          simpa [AuxNode.truncate, hfi] using hb
        calc
          (infiniteAuxCanonicalMap hS (j + 1) a).val.bit (f i) =
            (infiniteAuxCanonicalMap hS j (a.truncate j)).val.bit (f i) :=
              hprev
          _ = (a.truncate j).bit i := ih i hij (a.truncate j)
          _ = a.bit i := by simp [AuxNode.truncate, hij]

end CoordNode
end ThreeUniformDiaries
