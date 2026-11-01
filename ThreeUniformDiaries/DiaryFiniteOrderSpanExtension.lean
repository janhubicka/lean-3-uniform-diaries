import ThreeUniformDiaries.DiaryCountableRelativeStepExtension

/-!
# Finite numerical spacing exactly characterizes pure order extension

The canonical finite support of a countable diary may omit source
vertices between two selected vertices. An admissible map need not
reserve enough target levels for those future source vertices.

We prove the *exact* order-only condition for a prescribed finite
map f on a finite set S containing zero: it extends to a strictly
increasing total map Nat -> Nat iff every supported source interval
[x,y] gets at least y-x target steps.

The constructive direction uses a nondecreasing finite maximum
of the offsets f(s)-s over source support points s<=n. It neither
requires marker fixing nor asserts ANY diary-role, edge, meet,
generic leaf-range, or relative successor realization.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Pure numerical spacing on a finite set, without a target
hypergraph structure or a hidden infinite-extension predicate. -/
def FiniteOrderSpan (S : Finset Nat) (f : Nat → Nat) : Prop :=
  ∀ x y : Nat, x ∈ S → y ∈ S →
    x < y → f x + (y - x) ≤ f y

/-- The maximum of the nonnegative slacks already visible
at supported source vertices not exceeding n. -/
noncomputable def finiteOrderSlack
    (S : Finset Nat) (f : Nat → Nat) (n : Nat) : Nat :=
  (S.filter (fun s => s ≤ n)).sup (fun s => f s - s)

/-- Enlarging a prefix cannot decrease its maximum slack. -/
theorem finiteOrderSlack_mono
    (S : Finset Nat) (f : Nat → Nat) :
    Monotone (finiteOrderSlack S f) := by
  intro x y hxy
  unfold finiteOrderSlack
  apply Finset.sup_le
  intro s hs
  obtain ⟨hsS,hsx⟩ := Finset.mem_filter.mp hs
  have hsy : s ∈ S.filter (fun t => t ≤ y) :=
    Finset.mem_filter.mpr ⟨hsS,by omega⟩
  exact Finset.le_sup (f := fun t : Nat => f t - t) hsy

/-- Because zero belongs to the support, the spacing test
guarantees nonnegative slack even if f(0) is not zero. -/
theorem finiteOrderSpan_source_le
    {S : Finset Nat} {f : Nat → Nat}
    (hZero : 0 ∈ S)
    (hSpan : FiniteOrderSpan S f)
    (s : Nat) (hs : s ∈ S) :
    s ≤ f s := by
  by_cases hz : s = 0
  · subst s
    omega
  · have hPos : 0 < s := by omega
    have h := hSpan 0 s hZero hs hPos
    omega

/-- The visible maximum slack at any supported s is exactly
its own slack, because the spacing test makes the offsets
nondecreasing along the supported source order. -/
theorem finiteOrderSlack_at_mem
    {S : Finset Nat} {f : Nat → Nat}
    (hZero : 0 ∈ S)
    (hSpan : FiniteOrderSpan S f)
    (s : Nat) (hs : s ∈ S) :
    finiteOrderSlack S f s = f s - s := by
  classical
  unfold finiteOrderSlack
  apply le_antisymm
  · apply Finset.sup_le
    intro t ht
    obtain ⟨htS,hts⟩ := Finset.mem_filter.mp ht
    by_cases heq : t = s
    · subst t
      exact le_refl _
    · have hlt : t < s := by omega
      have hGap := hSpan t s htS hs hlt
      have hSource := finiteOrderSpan_source_le hZero hSpan t htS
      have hTarget := finiteOrderSpan_source_le hZero hSpan s hs
      omega
  · exact Finset.le_sup (f := fun t : Nat => f t - t)
      (Finset.mem_filter.mpr ⟨hs,le_refl s⟩)

/-- A finite spacing certificate constructs a total
strictly increasing order extension by adding the
nondecreasing maximum prefix slack. -/
theorem exists_strictMono_extension_of_finiteOrderSpan
    {S : Finset Nat} {f : Nat → Nat}
    (hZero : 0 ∈ S)
    (hSpan : FiniteOrderSpan S f) :
    ∃ g : Nat → Nat,
      StrictMono g ∧
      (∀ s : Nat, s ∈ S → g s = f s) := by
  classical
  let g : Nat → Nat := fun n => n + finiteOrderSlack S f n
  refine ⟨g,?_,?_⟩
  · intro x y hxy
    have hSlack : finiteOrderSlack S f x ≤
        finiteOrderSlack S f y :=
      finiteOrderSlack_mono S f (Nat.le_of_lt hxy)
    change x + finiteOrderSlack S f x <
      y + finiteOrderSlack S f y
    omega
  · intro s hs
    have hEq := finiteOrderSlack_at_mem hZero hSpan s hs
    have hSource := finiteOrderSpan_source_le hZero hSpan s hs
    change s + finiteOrderSlack S f s = f s
    rw [hEq]
    omega

private theorem strictMono_nat_preserves_gap
    {g : Nat → Nat} (hg : StrictMono g)
    {x y : Nat} (hxy : x ≤ y) :
    g x + (y - x) ≤ g y := by
  induction y, hxy using Nat.le_induction with
  | base => simp
  | succ y hxy ih =>
      have hStep : g y < g (y + 1) :=
        hg (Nat.lt_succ_self y)
      omega

/-- Exact finite iff, with no reference to the diary
extension theorem. This solves all pure ordering constraints,
but none of the target role, edge or meet realization constraints. -/
theorem finiteOrderSpan_iff_strictMono_extension
    {S : Finset Nat} {f : Nat → Nat}
    (hZero : 0 ∈ S) :
    FiniteOrderSpan S f ↔
    ∃ g : Nat → Nat, StrictMono g ∧
      (∀ s : Nat, s ∈ S → g s = f s) := by
  constructor
  · exact exists_strictMono_extension_of_finiteOrderSpan hZero
  · rintro ⟨g,hMono,hFix⟩
    intro x y hx hy hxy
    have hGap := strictMono_nat_preserves_gap hMono (Nat.le_of_lt hxy)
    rw [hFix x hx,hFix y hy] at hGap
    exact hGap

end DiaryLeafPriority
end ThreeUniformDiaries
