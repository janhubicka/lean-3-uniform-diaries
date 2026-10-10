import ThreeUniformDiaries.FiniteCoupledCanonicalMapSucc
import ThreeUniformDiaries.FiniteActualCandidateMeetClosure
import ThreeUniformDiaries.FiniteSelectedSuccessorBridge

/-!
# Prescribed singleton types under the concrete finite canonical map

Suppose the constructed auxiliary canonical map has already been
identified with target pair types on genuine source pairs. The
triangular E1 recursion then sends the singleton type of each actual
source vertex v over cut i to precisely the target singleton type of
f(v) over f(i).

The proof uses only the true finite embedding interface, E1 candidate
inclusion, an explicit first-root identity, and the constructed E1
successor-cone law. It makes no assertion about artificial source
vertices after m.

The two extra assumptions (auxiliary candidate-image identity and
singleton root identity) are separate mathematical lemmas established
in the E2 and E1 root files, rather than hidden in the induction.
-/

namespace ThreeUniformDiaries
namespace EnumNode

theorem finiteOneCanonicalMap_prescribed_vertexTypes
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (f : Nat → Nat)
    (hf : Ordered3Graph.FiniteAuxEmbedding
      A.toOrdered3Graph H.toOrdered3Graph f m)
    (n : Nat) (hfix : ∀ j < n, f j = j)
    {S₁ S₂ : Set CoordNode}
    {r₁ : OneNode (f 0)} {r₂ : AuxNode (f 0)}
    (h₁ : CoordNode.FiniteStrongPicture S₁ f (m - 1)
      (.one (f 0) r₁))
    (h₂ : CoordNode.FiniteStrongPicture S₂ f (m - 1)
      (.aux (f 0) r₂))
    (hinc : ∀ x, finiteOneCandidate A H f n x → x ∈ S₁)
    (hroot : ∀ v : Nat, v < m →
      r₁ = H.oneType (f 0) (f v))
    (haux : ∀ (j v : Nat) (hjv : j < v) (hvm : v < m),
      (CoordNode.finiteStrongPicture_auxCanonicalMap h₂ j
        (by omega) (A.auxType j j v)).val =
          H.auxType (f j) (f j) (f v))
    (i v : Nat) (hiv : i ≤ v) (hvm : v < m) :
    (CoordNode.finiteStrongPicture_oneCanonicalMap h₁ h₂ i
      (by omega) (A.oneType i v)).val =
        H.oneType (f i) (f v) := by
  have hmain :
      ∀ (j : Nat) (hjv : j ≤ v),
      (CoordNode.finiteStrongPicture_oneCanonicalMap h₁ h₂ j
        (by omega) (A.oneType j v)).val =
          H.oneType (f j) (f v) := by
    intro j
    induction j with
    | zero =>
        intro _
        simpa using hroot v hvm
    | succ j ih =>
        intro hjv
        have hjlt : j < v := by omega
        have hjk : j < m - 1 := by omega
        have hjprev := ih (by omega)
        have hauxj := haux j v hjlt hvm
        have hsrc :
            A.oneType (j + 1) v =
              (A.oneType j v).succ (A.auxType j j v) := by
          apply OneNode.ext_pairs
          funext a b
          exact A.oneType_succ_pair
            (l := j) (v := v) (i := a) (j := b)
        have hmap :=
          CoordNode.finiteStrongPicture_oneCanonicalMap_succ
            h₁ h₂ j hjk (A.oneType j v) (A.auxType j j v)
        rw [← hsrc] at hmap
        rw [hjprev, hauxj] at hmap
        let old := H.oneType (f j) (f v)
        let param := H.auxType (f j) (f j) (f v)
        let target := H.oneType (f (j + 1)) (f v)
        have hprevMem : CoordNode.one (f j) old ∈ S₁ := by
          have hmem :=
            (CoordNode.finiteStrongPicture_oneCanonicalMap h₁ h₂ j
              (by omega) (A.oneType j v)).property
          simpa only [hjprev] using hmem
        have htargetMem : CoordNode.one (f (j + 1)) target ∈ S₁ := by
          by_cases hprefix : j + 1 < n
          · have hfixj : f (j + 1) = j + 1 :=
              hfix (j + 1) hprefix
            apply hinc
            exact Or.inl ⟨f (j + 1), target,
              by rw [hfixj]; exact hprefix, rfl⟩
          · apply hinc
            exact Or.inr ⟨j + 1, v,
              Nat.le_of_not_gt hprefix, (by omega), hvm, rfl⟩
        have htargetCone :
            CoordNode.one (f j + 1) (old.succ param) ≤
              CoordNode.one (f (j + 1)) target := by
          have hstep : f j + 1 ≤ f (j + 1) :=
            Nat.succ_le_of_lt
              (hf.strictMono (Nat.lt_succ_self j))
          refine ⟨hstep, ?_⟩
          change CoordNode.one (f j + 1)
              (target.truncate (f j + 1)) =
            CoordNode.one (f j + 1) (old.succ param)
          exact congrArg (CoordNode.one (f j + 1))
            (finite_selected_one_successor H f hf.strictMono j v)
        obtain ⟨b, hb, hunique⟩ :=
          CoordNode.finiteStrongPicture_one_lift
            h₁ j hjk old hprevMem param
        have hmapEq :
            (CoordNode.finiteStrongPicture_oneCanonicalMap h₁ h₂
              (j + 1) (by omega) (A.oneType (j + 1) v)).val = b :=
          hunique _ ⟨
            (CoordNode.finiteStrongPicture_oneCanonicalMap h₁ h₂
              (j + 1) (by omega) (A.oneType (j + 1) v)).property,
            hmap⟩
        have htargetEq : target = b :=
          hunique _ ⟨htargetMem, htargetCone⟩
        exact hmapEq.trans htargetEq.symm
  exact hmain i hiv

end EnumNode
end ThreeUniformDiaries
