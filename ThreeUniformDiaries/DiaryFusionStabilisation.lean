import ThreeUniformDiaries.DiaryFusion
import ThreeUniformDiaries.DiaryFullRoleDefinition

/-!
# Transferring diary stabilisation invariants through countable fusion

Once the actual lower-bound stage recursion produces a prefix-stable
chain, the remaining limit arguments are entirely finite: evaluate
each finite configuration at one stage after every relevant vertex
has stabilised. The outer map F need not be order-preserving.

This module verifies the three outputs of the manuscript's
type-stabilisation lemma *from their corresponding persistent stage
invariants*: order preservation, singleton-type stabilisation, and
pair-type plus lexicographic-orientation stabilisation.

The hypotheses are the stage invariants themselves. Producing those
invariants from generic avoidance and the finite family ATR theorem
is a separate construction and is not asserted here.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph
namespace Embedding

variable {H K : Ordered3Graph Nat}

/-- Increasing outer images of every finite stage prefix ensure that
the fused outer image is strictly increasing. No order assumption on
the original ambient map is required. -/
theorem fusion_order_preserved
    (F : Nat → Nat)
    (g : Nat → Embedding H H)
    (hs : PrefixStable g)
    (horder : ∀ k u v, u < v → v < k →
      F (g k u) < F (g k v)) :
    StrictMono (fun t => F ((fusionEmbedding g hs) t)) := by
  intro u v huv
  let k := v + 1
  have hu : u < k := by dsimp [k]; omega
  have hv : v < k := by dsimp [k]; omega
  have h := horder k u v huv hv
  have eqU := fusionEmbedding_eq_stage g hs k u hu
  have eqV := fusionEmbedding_eq_stage g hs k v hv
  simpa only [eqU, eqV] using h

/-- The singleton stabilisation conclusion at cut i survives fusion
if every stage from i onwards satisfies the same fixed-cut invariant.
The predecessor image is stable because i-1 lies in the protected
prefix. -/
theorem fusion_one_type_stabilised
    (F : Nat → Nat)
    (g : Nat → Embedding H H)
    (hs : PrefixStable g)
    (i : Nat) (hi : 0 < i)
    (hstage : ∀ k, i ≤ k →
      ∀ u v, i ≤ u → i ≤ v →
        H.SameOneTypeBelow i u v →
        K.SameOneTypeBelow (F (g k (i-1)) + 1)
          (F (g k u)) (F (g k v))) :
    ∀ u v, i ≤ u → i ≤ v →
      H.SameOneTypeBelow i u v →
      K.SameOneTypeBelow (F ((fusionEmbedding g hs) (i-1)) + 1)
        (F ((fusionEmbedding g hs) u))
        (F ((fusionEmbedding g hs) v)) := by
  intro u v hiu hiv htype
  let k := i + u + v + 1
  have hik : i ≤ k := by dsimp [k]; omega
  have hprev : i - 1 < k := by dsimp [k]; omega
  have hu : u < k := by dsimp [k]; omega
  have hv : v < k := by dsimp [k]; omega
  have h := hstage k hik u v hiu hiv htype
  have eqPrev := fusionEmbedding_eq_stage g hs k (i-1) hprev
  have eqU := fusionEmbedding_eq_stage g hs k u hu
  have eqV := fusionEmbedding_eq_stage g hs k v hv
  simpa only [eqPrev, eqU, eqV] using h

/-- The pointed-pair part of stabilisation—including orientation—is
also inherited by the fusion. The premise is intentionally the
persistent stage invariant; it may be established just for diary
leaf pairs by replacing the source-class hypothesis. -/
theorem fusion_two_type_and_orientation_stabilised
    (F : Nat → Nat)
    (g : Nat → Embedding H H)
    (hs : PrefixStable g)
    (i : Nat) (hi : 0 < i)
    (hstage : ∀ k, i ≤ k →
      ∀ a b c d, i ≤ a → a < b → i ≤ c → c < d →
        H.SameTwoTypeBelow i a b c d →
        K.SameTwoTypeBelow (F (g k (i-1)) + 1)
          (F (g k a)) (F (g k b))
          (F (g k c)) (F (g k d)) ∧
        (DiaryLeafPriority.LexEarlier K (F (g k a)) (F (g k b)) ↔
         DiaryLeafPriority.LexEarlier K (F (g k c)) (F (g k d)))) :
    ∀ a b c d, i ≤ a → a < b → i ≤ c → c < d →
      H.SameTwoTypeBelow i a b c d →
      K.SameTwoTypeBelow
        (F ((fusionEmbedding g hs) (i-1)) + 1)
        (F ((fusionEmbedding g hs) a))
        (F ((fusionEmbedding g hs) b))
        (F ((fusionEmbedding g hs) c))
        (F ((fusionEmbedding g hs) d)) ∧
      (DiaryLeafPriority.LexEarlier K
          (F ((fusionEmbedding g hs) a))
          (F ((fusionEmbedding g hs) b)) ↔
       DiaryLeafPriority.LexEarlier K
          (F ((fusionEmbedding g hs) c))
          (F ((fusionEmbedding g hs) d))) := by
  intro a b c d hia hab hic hcd htype
  let k := i + a + b + c + d + 1
  have hik : i ≤ k := by dsimp [k]; omega
  have hprev : i - 1 < k := by dsimp [k]; omega
  have ha : a < k := by dsimp [k]; omega
  have hb : b < k := by dsimp [k]; omega
  have hc : c < k := by dsimp [k]; omega
  have hd : d < k := by dsimp [k]; omega
  have h := hstage k hik a b c d hia hab hic hcd htype
  have eqPrev := fusionEmbedding_eq_stage g hs k (i-1) hprev
  have eqA := fusionEmbedding_eq_stage g hs k a ha
  have eqB := fusionEmbedding_eq_stage g hs k b hb
  have eqC := fusionEmbedding_eq_stage g hs k c hc
  have eqD := fusionEmbedding_eq_stage g hs k d hd
  simpa only [eqPrev, eqA, eqB, eqC, eqD] using h

end Embedding
end Ordered3Graph
end ThreeUniformDiaries
