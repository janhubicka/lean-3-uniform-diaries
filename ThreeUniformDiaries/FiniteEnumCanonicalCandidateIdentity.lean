import ThreeUniformDiaries.FiniteOneCanonicalCandidateIdentity
import ThreeUniformDiaries.FiniteEnumMeetClosure

/-!
# Prescribed enumeration prefixes under the concrete finite map

Once the constructed singleton canonical map sends source singleton
types to the corresponding selected target singleton types, the
constructed enumeration canonical map sends the entire source
enumeration prefix A|i to the literal target prefix H|f(i).

The proof is a direct induction using the real E0 candidate carrier,
the source and target enumeration successor equations and strong
child-cone uniqueness. The hypotheses isolate the E1 candidate-image
identity and E0 root equality already treated in earlier modules.
-/

namespace ThreeUniformDiaries
namespace EnumNode

theorem finiteEnumCanonicalMap_prescribed_prefixes
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (f : Nat → Nat) (hf : StrictMono f)
    (n : Nat) (hfix : ∀ j < n, f j = j)
    {S₀ S₁ S₂ : Set CoordNode}
    {r₀ : EnumNode (f 0)} {r₁ : OneNode (f 0)}
    {r₂ : AuxNode (f 0)}
    (h₀ : CoordNode.FiniteStrongPicture S₀ f (m - 1)
      (.enum (f 0) r₀))
    (h₁ : CoordNode.FiniteStrongPicture S₁ f (m - 1)
      (.one (f 0) r₁))
    (h₂ : CoordNode.FiniteStrongPicture S₂ f (m - 1)
      (.aux (f 0) r₂))
    (hinc : ∀ x, finiteEnumCandidate H f n m x → x ∈ S₀)
    (hroot : r₀ = H.truncate (f 0))
    (hone : ∀ j : Nat, j < m →
      (CoordNode.finiteStrongPicture_oneCanonicalMap h₁ h₂ j
        (by omega) (A.oneType j j)).val =
        H.oneType (f j) (f j))
    (i : Nat) (him : i < m) :
    (CoordNode.finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ i
      (by omega) (A.truncate i)).val =
        H.truncate (f i) := by
  have hmain :
      ∀ (j : Nat) (hjm : j < m),
      (CoordNode.finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂ j
        (by omega) (A.truncate j)).val =
          H.truncate (f j) := by
    intro j
    induction j with
    | zero =>
        intro _
        simpa using hroot
    | succ j ih =>
        intro hjm
        have hjk : j < m - 1 := by omega
        have hjprev := ih (by omega)
        have honej := hone j (by omega)
        have hsrc :
            A.truncate (j + 1) =
              (A.truncate j).succ (A.oneType j j) := by
          apply EnumNode.ext_triples
          funext a b c
          exact A.truncate_succ_triple
            (l := j) (i := a) (j := b) (k := c)
        have hmap :=
          CoordNode.finiteStrongPicture_enumCanonicalMap_succ
            h₀ h₁ h₂ j hjk (A.truncate j) (A.oneType j j)
        rw [← hsrc] at hmap
        rw [hjprev, honej] at hmap
        let old := H.truncate (f j)
        let param := H.oneType (f j) (f j)
        let target := H.truncate (f (j + 1))
        have hprevMem : CoordNode.enum (f j) old ∈ S₀ := by
          have hmem :=
            (CoordNode.finiteStrongPicture_enumCanonicalMap
              h₀ h₁ h₂ j (by omega) (A.truncate j)).property
          simpa only [hjprev] using hmem
        have htargetMem : CoordNode.enum (f (j + 1)) target ∈ S₀ := by
          by_cases hprefix : j + 1 < n
          · have hfixj : f (j + 1) = j + 1 :=
              hfix (j + 1) hprefix
            apply hinc
            exact Or.inl ⟨f (j + 1), target,
              by rw [hfixj]; exact hprefix, rfl⟩
          · apply hinc
            exact Or.inr ⟨j + 1, Nat.le_of_not_gt hprefix,
              hjm, rfl⟩
        have htargetCone :
            CoordNode.enum (f j + 1) (old.succ param) ≤
              CoordNode.enum (f (j + 1)) target := by
          have hstep : f j + 1 ≤ f (j + 1) :=
            Nat.succ_le_of_lt (hf (Nat.lt_succ_self j))
          refine ⟨hstep, ?_⟩
          change CoordNode.enum (f j + 1)
              (target.truncate (f j + 1)) =
            CoordNode.enum (f j + 1) (old.succ param)
          exact congrArg (CoordNode.enum (f j + 1))
            (finite_selected_enum_successor H f hf j)
        obtain ⟨b, hb, hunique⟩ :=
          CoordNode.finiteStrongPicture_enum_lift
            h₀ j hjk old hprevMem param
        have hmapEq :
            (CoordNode.finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂
              (j + 1) (by omega) (A.truncate (j + 1))).val = b :=
          hunique _ ⟨
            (CoordNode.finiteStrongPicture_enumCanonicalMap h₀ h₁ h₂
              (j + 1) (by omega) (A.truncate (j + 1))).property,
            hmap⟩
        have htargetEq : target = b :=
          hunique _ ⟨htargetMem, htargetCone⟩
        exact hmapEq.trans htargetEq.symm
  exact hmain i him

end EnumNode
end ThreeUniformDiaries
