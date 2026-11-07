import ThreeUniformDiaries.DiaryFiniteSingletonColour
import ThreeUniformDiaries.DiaryFullNewGeneratorProfileStabilisation

/-!
# A cofinal mixed singleton type cone from the EXISTING finite colour

The lower-bound library already has the exact mask
  DiaryLowerBoundColors.singletonColour K B v : Fin B -> Fin B -> Bool
and the proved equation
  singletonColour K B v = singletonColour K B w
       iff K.SameOneTypeBelow B v w.

We REUSE that checked API rather than duplicate a second finite code.
By finite_choice_persistent_of_downward_type, one colour of ANY
sequence F(n) recurs at arbitrarily large input indices.

If F:Nat->Nat is injective, its values eventually exceed every fixed
numerical bound. Therefore one code has arbitrarily large TARGET
images in F[Nat], even if F is not increasing.

CRITICAL: the recurrent type is not prescribed in advance and
need not be the type required by a fixed diary old stage; nor does
cofinal recurrence give any persistent next-leaf choice. This is
not an unconditional countable diary unavoidability theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Some EXISTING lower-bound singleton colour occurs at arbitrarily
large outer source indices, for ANY specified function F. -/
theorem exists_cofinal_existing_singletonColour
    (K : Ordered3Graph Nat) (B : Nat) (F : Nat → Nat) :
    ∃ p : Fin B → Fin B → Bool,
      ∀ N : Nat, ∃ n : Nat, N ≤ n ∧
        DiaryLowerBoundColors.singletonColour K B (F n) = p := by
  classical
  let C := Fin B → Fin B → Bool
  let colour : Nat → C := fun n =>
    DiaryLowerBoundColors.singletonColour K B (F n)
  let R : C → Nat → Prop := fun p N =>
    ∃ n : Nat, N ≤ n ∧ colour n = p
  have hDown : ∀ (p : C) (N M : Nat),
      M ≤ N → R p N → R p M := by
    intro p N M hMN
    rintro ⟨n,hn,hc⟩
    exact ⟨n, hMN.trans hn, hc⟩
  have hCover : ∀ N : Nat,
      ∃ p : C, p ∈ (Finset.univ : Finset C) ∧ R p N := by
    intro N
    exact ⟨colour N,Finset.mem_univ _,N,le_rfl,rfl⟩
  obtain ⟨p,_hMem,hCofinal⟩ :=
    finite_choice_persistent_of_downward_type
      (Finset.univ : Finset C) R hDown hCover
  exact ⟨p,hCofinal⟩

/-- For an injection of Nat into Nat, all sufficiently LATE input
indices map ABOVE any prescribed finite target bound. This is
stronger than the already verified unboundedness of its range,
but is still an elementary finite-preimage argument. -/
theorem injective_nat_eventually_above_bound
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

/-- SOME actual mixed singleton colour is recurrent on target
vertices of arbitrarily large numerical index, if F is injective.
The chosen colour can differ from the colour of a prescribed
already selected leaf of a reserved stage. -/
theorem exists_unbounded_existing_singletonColour_fiber
    (K : Ordered3Graph Nat) (B : Nat)
    (F : Nat → Nat) (hInj : Function.Injective F) :
    ∃ p : Fin B → Fin B → Bool,
      ∀ M : Nat, ∃ n : Nat, M < F n ∧
        DiaryLowerBoundColors.singletonColour K B (F n) = p := by
  obtain ⟨p,hCofinal⟩ :=
    exists_cofinal_existing_singletonColour K B F
  refine ⟨p,?_⟩
  intro M
  obtain ⟨N,hLarge⟩ := injective_nat_eventually_above_bound F hInj M
  obtain ⟨n,hn,hColour⟩ := hCofinal N
  exact ⟨n,hLarge n hn,hColour⟩

end DiaryLeafPriority
end ThreeUniformDiaries
