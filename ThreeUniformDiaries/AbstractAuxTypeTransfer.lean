import ThreeUniformDiaries.TypeCutTransfer

/-!
# From inherited-gap tests to aux-type-respecting embeddings

This is the final abstract transfer step of Lemma Kiemb.  The
selected/omitted decomposition and edge reflection show that an induced
embedding is aux-type-respecting whenever two concrete target
conditions hold for the image of the source:

* at every source singleton-type agreement cut, pairs with an endpoint
  outside the image have equal edge bits;
* a vertex outside the image gives no auxiliary edge test through
  an increasing pair of selected vertices above the cut.

The converse implications for both kinds of type agreement follow
automatically from edge reflection and strict monotonicity. No
"bounded defect" or assumption that the image is convex is used.

The remaining concrete task is to discharge the two hypotheses for
each canonical branch in the size-first K_I construction.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph
namespace Embedding

variable {H G : Ordered3Graph Nat} (f : Embedding H G)

/-- All omitted-pair singleton-type comparisons needed below
a selected cut at which the source singleton types agree. -/
def OmittedOneAgreement : Prop :=
  ∀ (w u v : Nat), w ≤ u → w ≤ v →
    H.SameOneTypeBelow w u v →
    ∀ (x y : Nat), x < y → y < f w →
      ((¬ ∃ a : Nat, f a = x) ∨ (¬ ∃ b : Nat, f b = y)) →
      (G.edge x y (f u) ↔ G.edge x y (f v))

/-- Omitted target vertices do not contribute auxiliary tests for
increasing selected pairs above the cut. -/
def OmittedAuxZero : Prop :=
  ∀ (w u₀ u₁ : Nat), w ≤ u₀ → u₀ < u₁ →
    ∀ (x : Nat), x < f w →
      (¬ ∃ a : Nat, f a = x) →
      ¬ G.edge x (f u₀) (f u₁)

/-- The selected/omitted comparison together with edge reflection
completes the aux-type-respecting conclusion. -/
theorem auxTypeRespecting_of_omitted
    (hOne : f.OmittedOneAgreement) (hAux : f.OmittedAuxZero) :
    f.AuxTypeRespecting := by
  constructor
  · intro w u v hwu hwv
    constructor
    · intro hsource
      exact oneTypeAgreement_transfer H G f f.strictMono
        (fun a b c hab hbc => f.edge_iff hab hbc)
        w u v hwu hwv hsource
        (hOne w u v hwu hwv hsource)
    · intro htarget
      intro a b hab hbw
      have hbu : b < u := lt_of_lt_of_le hbw hwu
      have hbv : b < v := lt_of_lt_of_le hbw hwv
      calc
        H.edge a b u ↔ G.edge (f a) (f b) (f u) :=
          f.edge_iff hab hbu
        _ ↔ G.edge (f a) (f b) (f v) :=
          htarget (f.strictMono hab) (f.strictMono hbw)
        _ ↔ H.edge a b v := (f.edge_iff hab hbv).symm
  · intro w u₀ u₁ v₀ v₁ hwu hu hwv hv
    constructor
    · intro hsource
      apply auxTypeAgreement_transfer H G f f.strictMono
        (fun a b c hab hbc => f.edge_iff hab hbc)
        w u₀ u₁ v₀ v₁ hwu hu hwv hv hsource
      intro x hxw hx
      exact ⟨hAux w u₀ u₁ hwu hu x hxw hx,
        hAux w v₀ v₁ hwv hv x hxw hx⟩
    · intro htarget
      intro a haw
      have hau : a < u₀ := lt_of_lt_of_le haw hwu
      have hav : a < v₀ := lt_of_lt_of_le haw hwv
      calc
        H.edge a u₀ u₁ ↔ G.edge (f a) (f u₀) (f u₁) :=
          f.edge_iff hau hu
        _ ↔ G.edge (f a) (f v₀) (f v₁) :=
          htarget (f.strictMono haw)
        _ ↔ H.edge a v₀ v₁ := (f.edge_iff hav hv).symm

end Embedding
end Ordered3Graph
end ThreeUniformDiaries
