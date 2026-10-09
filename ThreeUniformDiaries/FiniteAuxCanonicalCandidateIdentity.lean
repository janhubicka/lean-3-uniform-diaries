import ThreeUniformDiaries.FiniteAuxCanonicalMapSucc
import ThreeUniformDiaries.FiniteAuxCandidateSuccessor

/-!
# The constructed auxiliary canonical map hits all prescribed pair types

This is the first full candidate-image induction for the finite
converse Aemb: the concrete recursively defined auxiliary map sends
each source pair type over an actual finite source cut i to the
corresponding target pair type over the selected cut f(i).

The only extra base premise explicitly identifies the selected initial
root with every relevant target pair type at f(0). This is the separate
root assertion supplied by the finite-embedding type-agreement
hypotheses (and is vacuous if there is no actual source pair).

All inductive steps use the actual finite embedding hypotheses, the
prescribed E2^- candidate carrier, exact edge bits and typed strong
successor uniqueness. No artificial source vertices or abstract
CanonicalMap structure are used.
-/

namespace ThreeUniformDiaries
namespace EnumNode

theorem finiteAuxCanonicalMap_prescribed_pairTypes
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (f : Nat → Nat)
    (hf : Ordered3Graph.FiniteAuxEmbedding
      A.toOrdered3Graph H.toOrdered3Graph f m)
    (n : Nat) (hfix : ∀ j < n, f j = j)
    {S : Set CoordNode} {r : AuxNode (f 0)}
    (hS : CoordNode.FiniteStrongPicture S f (m - 1)
      (.aux (f 0) r))
    (hinc : ∀ x, finiteAuxCandidate A H f n x → x ∈ S)
    (hroot : ∀ u v : Nat, u < v → v < m →
      r = H.auxType (f 0) (f u) (f v))
    (i u v : Nat) (hiu : i ≤ u) (huv : u < v) (hvm : v < m) :
    (CoordNode.finiteStrongPicture_auxCanonicalMap hS i
      (by omega) (A.auxType i u v)).val =
        H.auxType (f i) (f u) (f v) := by
  have hmain :
      ∀ j : Nat, j ≤ u →
        (CoordNode.finiteStrongPicture_auxCanonicalMap hS j
          (by omega) (A.auxType j u v)).val =
          H.auxType (f j) (f u) (f v) := by
    intro j
    induction j with
    | zero =>
        intro _
        simpa using hroot u v huv hvm
    | succ j ih =>
        intro hju
        have hjlt : j < u := by omega
        have hjk : j < m - 1 := by omega
        have hjprev := ih (by omega)
        have hsrc :
            A.auxType (j + 1) u v =
              (A.auxType j u v).succ (A.triple j u v) := by
          apply AuxNode.ext_bits
          funext a
          exact A.auxType_succ_bit
            (l := j) (u := u) (v := v) (i := a)
        have hmap := CoordNode.finiteStrongPicture_auxCanonicalMap_succ
          hS j hjk (A.auxType j u v) (A.triple j u v)
        rw [← hsrc] at hmap
        rw [hjprev] at hmap
        let old := H.auxType (f j) (f u) (f v)
        let bit := A.triple j u v
        let target := H.auxType (f (j + 1)) (f u) (f v)
        have hprevMem :
            CoordNode.aux (f j) old ∈ S := by
          have hmem :=
            (CoordNode.finiteStrongPicture_auxCanonicalMap hS j
              (by omega) (A.auxType j u v)).property
          simpa only [hjprev] using hmem
        have htargetMem :
            CoordNode.aux (f (j + 1)) target ∈ S := by
          by_cases hprefix : j + 1 < n
          · have hfixj : f (j + 1) = j + 1 :=
              hfix (j + 1) hprefix
            apply hinc
            exact Or.inl ⟨j + 1, target, hprefix,
              by simp [target, hfixj]⟩
          · apply hinc
            exact Or.inr ⟨j + 1, u, v,
              Nat.le_of_not_gt hprefix, Nat.le_of_lt hjlt,
              huv, hvm, rfl⟩
        have htargetCone :
            CoordNode.aux (f j + 1) (old.succ bit) ≤
              CoordNode.aux (f (j + 1)) target := by
          have hstep : f j + 1 ≤ f (j + 1) := by
            have hh := hf.strictMono (Nat.lt_succ_self j)
            omega
          refine ⟨hstep, ?_⟩
          change CoordNode.aux (f j + 1)
              (target.truncate (f j + 1)) =
            CoordNode.aux (f j + 1) (old.succ bit)
          exact congrArg (CoordNode.aux (f j + 1))
            (finite_selected_aux_successor A H f hf j u v
              hjlt huv hvm)
        obtain ⟨b, hb, hunique⟩ :=
          CoordNode.finiteStrongPicture_aux_lift
            hS j hjk old hprevMem bit
        have hmapEq :
            (CoordNode.finiteStrongPicture_auxCanonicalMap hS
              (j + 1) (by omega) (A.auxType (j + 1) u v)).val = b :=
          hunique _ ⟨
            (CoordNode.finiteStrongPicture_auxCanonicalMap hS
              (j + 1) (by omega) (A.auxType (j + 1) u v)).property,
            hmap⟩
        have htargetEq : target = b :=
          hunique _ ⟨htargetMem, htargetCone⟩
        exact hmapEq.trans htargetEq.symm
  exact hmain i hiu

end EnumNode
end ThreeUniformDiaries
