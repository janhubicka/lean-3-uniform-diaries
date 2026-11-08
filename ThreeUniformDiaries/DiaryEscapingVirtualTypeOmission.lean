import ThreeUniformDiaries.DiaryMonochromaticLeafMeetObstruction
import ThreeUniformDiaries.DiarySingletonColourCofinalCone

/-!
# Track D: escaping genuine leaf sequences necessarily omit their recurrent full type

In a genuine full RoleDiary, the S1 one-split axiom makes distinct
target leaf vertices distinguishable already by their COMPLETE mixed
singleton colours at a finite cut. This implies a stronger regression:
along any sequence of genuine leaves whose numeric images escape
every bounded target interval, the colour of a FIXED leaf u at cut u
is eventually absent.

Consequently any coherent countable virtual singleton type obtained
as a cofinally recurring finite-colour limit along an escaping
sequence is NOT realized by ANY target leaf. No countable saturation
or monotonicity assumptions are invoked.

An injective sequence of target leaves escapes automatically by
the existing finite-preimage lemma. The observation is directly
relevant to the escaping branch of the pending relative next-leaf
fusion argument: repeated mixed finite types can describe a type
absent from the actual full diary. It is NOT a contradiction to
countable diary unavoidability and supplies no persistent successor.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Once all terms v(n) have passed a fixed genuine leaf u,
their complete singleton colours at cut u differ from the
actual singleton colour of u. This is a direct consequence
of the exact S1-meet separation of distinct genuine leaves. -/
theorem RoleDiary.eventually_avoids_fixed_leaf_colour
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (u : Nat) (hu : IsLeaf K u)
    (v : Nat → Nat) (hv : ∀ n, IsLeaf K (v n))
    (hLater : ∃ N : Nat, ∀ n : Nat, N ≤ n → u < v n) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      DiaryLowerBoundColors.singletonColour K u (v n) ≠
        DiaryLowerBoundColors.singletonColour K u u := by
  obtain ⟨N, hN⟩ := hLater
  refine ⟨N, ?_⟩
  intro n hn hEqual
  have hlt : u < v n := hN n hn
  have hNe : u ≠ v n := ne_of_lt hlt
  have hDiff :
      DiaryLowerBoundColors.singletonColour K u u ≠
        DiaryLowerBoundColors.singletonColour K u (v n) := by
    have h :=
      DK.distinct_leaves_have_different_colour_at_min
        u (v n) hu (hv n) hNe
    simpa only [min_eq_left hlt.le] using h
  exact hDiff hEqual.symm

/-- Eventual numerical escape excludes the possibility that a
cofinally recurring coherent full mixed singleton type is
realized by any actual genuine leaf. The coherent projection
identities of c are not even needed for this implication. -/
theorem RoleDiary.escaping_recurrent_full_mixed_type_omitted
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (v : Nat → Nat) (hv : ∀ n, IsLeaf K (v n))
    (hEscape : ∀ B : Nat, ∃ N : Nat,
      ∀ n : Nat, N ≤ n → B < v n)
    (c : (B : Nat) → Fin B → Fin B → Bool)
    (hRecur : ∀ B N : Nat, ∃ n : Nat, N ≤ n ∧
      DiaryLowerBoundColors.singletonColour K B (v n) = c B) :
    ¬ ∃ u : Nat, IsLeaf K u ∧
      ∀ B : Nat,
        DiaryLowerBoundColors.singletonColour K B u = c B := by
  rintro ⟨u, hu, hAll⟩
  obtain ⟨N, hAvoid⟩ :=
    DK.eventually_avoids_fixed_leaf_colour u hu v hv (hEscape u)
  obtain ⟨n, hn, hColour⟩ := hRecur u N
  exact hAvoid n hn (hColour.trans (hAll u).symm)

/-- A sequence of genuine target leaves with INJECTIVE image
automatically eventually escapes every fixed target numerical
bound, even if it has no monotonicity. -/
theorem RoleDiary.injective_leaf_sequence_eventually_avoids_fixed_colour
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (u : Nat) (hu : IsLeaf K u)
    (v : Nat → Nat) (hv : ∀ n, IsLeaf K (v n))
    (hInj : Function.Injective v) :
    ∃ N : Nat, ∀ n : Nat, N ≤ n →
      DiaryLowerBoundColors.singletonColour K u (v n) ≠
        DiaryLowerBoundColors.singletonColour K u u := by
  exact DK.eventually_avoids_fixed_leaf_colour u hu v hv
    (injective_nat_eventually_above_bound v hInj u)

/-- In a full diary, a full mixed singleton type that recurs
cofinally along an injective sequence of genuine leaves must be
OMITTED by all actual genuine target leaves. This is a genuine
diary instance of non-saturation, unlike the generic-graph toy
counterexample; it does not disprove countable diary unavoidability. -/
theorem RoleDiary.injective_leaf_recurrent_full_mixed_type_omitted
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (v : Nat → Nat) (hv : ∀ n, IsLeaf K (v n))
    (hInj : Function.Injective v)
    (c : (B : Nat) → Fin B → Fin B → Bool)
    (hRecur : ∀ B N : Nat, ∃ n : Nat, N ≤ n ∧
      DiaryLowerBoundColors.singletonColour K B (v n) = c B) :
    ¬ ∃ u : Nat, IsLeaf K u ∧
      ∀ B : Nat,
        DiaryLowerBoundColors.singletonColour K B u = c B := by
  exact DK.escaping_recurrent_full_mixed_type_omitted v hv
    (fun B => injective_nat_eventually_above_bound v hInj B)
    c hRecur

end DiaryLeafPriority
end ThreeUniformDiaries
