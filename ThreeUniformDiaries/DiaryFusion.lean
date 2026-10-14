import ThreeUniformDiaries.AuxTypeRespectingComposition

/-!
# Countable fusion of prefix-stable embeddings

The diary lower-bound proof constructs a sequence of (aux-type-
respecting) embeddings g_i of the generic hypergraph, refining at
successive protected cuts. Later stages leave the earlier images
unchanged. This file proves that such a sequence has a genuine
limit embedding and, in fact, that full auxiliary-type respect
passes to the limit when it holds at every stage.

The proof is independent of the Ramsey construction generating
the stages. It does not assume uniform convergence on infinite
tails: every finite tuple is evaluated at ONE sufficiently late
stage where all of its coordinates have stabilised.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph
namespace Embedding

variable {H : Ordered3Graph Nat}

/-- Each successor embedding agrees with its predecessor on every
vertex strictly below the current protected cut. -/
def PrefixStable (g : Nat → Embedding H H) : Prop :=
  ∀ i t, t < i → g (i+1) t = g i t

/-- Once a vertex is below a protected stage i, every later stage
has exactly the same image of that vertex. -/
theorem prefixStable_add
    (g : Nat → Embedding H H) (hs : PrefixStable g)
    (i k t : Nat) (hti : t < i) :
    g (i+k) t = g i t := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      calc
        g (i + (k+1)) t = g ((i+k)+1) t := by rw [Nat.add_succ]
        _ = g (i+k) t := hs (i+k) t (by omega)
        _ = g i t := ih

/-- Alternative monotone-stage formulation of prefix stability. -/
theorem prefixStable_of_le
    (g : Nat → Embedding H H) (hs : PrefixStable g)
    (i k t : Nat) (hti : t < i) (hik : i ≤ k) :
    g k t = g i t := by
  have h := prefixStable_add g hs i (k-i) t hti
  have heq : i + (k-i) = k := by omega
  simpa only [heq] using h

/-- The pointwise fusion function reads vertex t from stage t+1,
after its image has become permanently fixed. -/
def fusionFunction (g : Nat → Embedding H H) (t : Nat) : Nat :=
  g (t+1) t

/-- Every finite protected prefix of the fusion function agrees
literally with the same prefix of any sufficiently late stage. -/
theorem fusionFunction_eq_stage
    (g : Nat → Embedding H H) (hs : PrefixStable g)
    (k t : Nat) (htk : t < k) :
    fusionFunction g t = g k t := by
  change g (t+1) t = g k t
  exact (prefixStable_of_le g hs (t+1) k t
    (Nat.lt_succ_self t) (by omega)).symm

/-- A prefix-stable chain of induced strictly increasing embeddings
has an induced strictly increasing limit. No genericity or
infinitary Ramsey axiom is needed. -/
def fusionEmbedding
    (g : Nat → Embedding H H) (hs : PrefixStable g) :
    Embedding H H where
  toFun := fusionFunction g
  strictMono := by
    intro x y hxy
    have hx : x < y+1 := by omega
    have h := fusionFunction_eq_stage g hs (y+1) x hx
    change fusionFunction g x < fusionFunction g y
    rw [h]
    exact (g (y+1)).strictMono hxy
  edge_iff := by
    intro x y z hxy hyz
    have hx : x < z+1 := by omega
    have hy : y < z+1 := by omega
    have h0 := fusionFunction_eq_stage g hs (z+1) x hx
    have h1 := fusionFunction_eq_stage g hs (z+1) y hy
    change H.edge x y z ↔
      H.edge (fusionFunction g x) (fusionFunction g y)
        (fusionFunction g z)
    rw [h0, h1]
    exact (g (z+1)).edge_iff hxy hyz

/-- The fused embedding inherits the literal initial-segment
agreement of every sufficiently late finite stage. -/
theorem fusionEmbedding_eq_stage
    (g : Nat → Embedding H H) (hs : PrefixStable g)
    (k t : Nat) (htk : t < k) :
    fusionEmbedding g hs t = g k t :=
  fusionFunction_eq_stage g hs k t htk

/-- If all finite stages preserve and reflect singleton and
auxiliary pair types, their pointwise fusion does too. For each
fixed tuple all relevant images coincide with a single stage. -/
theorem fusionEmbedding_auxTypeRespecting
    (g : Nat → Embedding H H) (hs : PrefixStable g)
    (haux : ∀ k, (g k).AuxTypeRespecting) :
    (fusionEmbedding g hs).AuxTypeRespecting := by
  constructor
  · intro l u v hlu hlv
    let k := l + u + v + 1
    have hl : l < k := by dsimp [k]; omega
    have hu : u < k := by dsimp [k]; omega
    have hv : v < k := by dsimp [k]; omega
    have h := (haux k).one l u v hlu hlv
    change H.SameOneTypeBelow l u v ↔
      H.SameOneTypeBelow (g k l) (g k u) (g k v) at h
    have eqL := fusionEmbedding_eq_stage g hs k l hl
    have eqU := fusionEmbedding_eq_stage g hs k u hu
    have eqV := fusionEmbedding_eq_stage g hs k v hv
    simpa only [eqL, eqU, eqV] using h
  · intro l a b c d hla hab hlc hcd
    let k := l + a + b + c + d + 1
    have hl : l < k := by dsimp [k]; omega
    have ha : a < k := by dsimp [k]; omega
    have hb : b < k := by dsimp [k]; omega
    have hc : c < k := by dsimp [k]; omega
    have hd : d < k := by dsimp [k]; omega
    have h := (haux k).aux l a b c d hla hab hlc hcd
    change H.SameAuxTypeBelow l a b c d ↔
      H.SameAuxTypeBelow (g k l) (g k a) (g k b)
        (g k c) (g k d) at h
    have eqL := fusionEmbedding_eq_stage g hs k l hl
    have eqA := fusionEmbedding_eq_stage g hs k a ha
    have eqB := fusionEmbedding_eq_stage g hs k b hb
    have eqC := fusionEmbedding_eq_stage g hs k c hc
    have eqD := fusionEmbedding_eq_stage g hs k d hd
    simpa only [eqL, eqA, eqB, eqC, eqD] using h

end Embedding
end Ordered3Graph
end ThreeUniformDiaries
