import ThreeUniformDiaries.DiaryCountableCoherentStrongEmbedding
import ThreeUniformDiaries.DiaryCountableRelativeStepExtension

/-!
# Future-order spacing is necessary for coherent countable diary fusion

An admissible map of a finite leaf-meet support may be increasing
without leaving room for the source vertices not yet in that support.
Any full increasing map of Nat satisfies the stronger quantitative
gap inequality: images of x < y differ by at least y-x.

We package this as an explicit finite constraint on each finite
support map, and prove it is necessary for any coherent limit.
This is a non-circular finite obstruction: the predicate examines
only a given stage, not the existence of a future embedding.

The pure-order converse (an order-only total extension whenever
the inequality holds on every pair in the finite support) is proved
in the companion manuscript audit note but is not asserted here.
The condition is NOT sufficient for diary role/edge/meet extension.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Every strictly increasing map of natural numbers reserves one
target level for every intervening source level. -/
theorem strictMono_nat_gap_bound
    {g : Nat → Nat} (hg : StrictMono g)
    {x y : Nat} (hxy : x ≤ y) :
    g x + (y - x) ≤ g y := by
  induction y, hxy using Nat.le_induction with
  | base =>
      simp
  | succ y hxy ih =>
      have hStep : g y < g (y + 1) :=
        hg (Nat.lt_succ_self y)
      omega

/-- A finite condition expressing enough numerical space between
the images of all currently supported source vertices to allow
eventual insertion of every missing source level, at least as a
pure order map. -/
def FutureOrderReserve (H : Ordered3Graph Nat)
    (m : Nat) (f : Nat → Nat) : Prop :=
  ∀ x y : Nat,
    x ∈ countableDiaryFiniteSupport H m →
    y ∈ countableDiaryFiniteSupport H m →
    x < y → f x + (y - x) ≤ f y

/-- Every full ordered embedding automatically has the explicit
finite reserve property on every canonical source support. -/
theorem futureOrderReserve_of_embedding
    {H K : Ordered3Graph Nat}
    (e : Ordered3Graph.Embedding H K) (m : Nat) :
    FutureOrderReserve H m e := by
  intro x y hx hy hxy
  exact strictMono_nat_gap_bound e.strictMono (Nat.le_of_lt hxy)

/-- More strongly, each stage of an actually coherent countable
diary-support system has the reserve property. Its proof uses the
already checked limit map and exact stage-to-limit compatibility,
not a new relative extension assumption. -/
theorem CoherentCofinalDiarySupportMaps.future_order_reserve
    {H K : Ordered3Graph Nat} {DH : RoleDiary H}
    (P : CoherentCofinalDiarySupportMaps DH K) (m : Nat) :
    FutureOrderReserve H m (P.map m) := by
  intro x y hx hy hxy
  have hGap :=
    strictMono_nat_gap_bound
      P.limit_is_diaryPreembedding.strictMono
      (Nat.le_of_lt hxy)
  rw [P.limit_eq_stage m x hx, P.limit_eq_stage m y hy] at hGap
  exact hGap

/-- If a finite stage compresses even one source gap below its
original numerical width, it cannot be the restriction of ANY
full ordered embedding of the source diary, regardless of
target genericity, role axioms, or finite flip absorption. -/
theorem no_full_diary_embedding_extending_compressed_stage
    {H K : Ordered3Graph Nat} {m : Nat} {f : Nat → Nat}
    (x y : Nat)
    (hx : x ∈ countableDiaryFiniteSupport H m)
    (hy : y ∈ countableDiaryFiniteSupport H m)
    (hxy : x < y)
    (hCompressed : f y < f x + (y - x)) :
    ¬ ∃ e : Ordered3Graph.Embedding H K,
      ∀ u : Nat, u ∈ countableDiaryFiniteSupport H m →
        e u = f u := by
  rintro ⟨e,hFix⟩
  have hGap :=
    strictMono_nat_gap_bound e.strictMono (Nat.le_of_lt hxy)
  rw [hFix x hx, hFix y hy] at hGap
  omega

end DiaryLeafPriority
end ThreeUniformDiaries
