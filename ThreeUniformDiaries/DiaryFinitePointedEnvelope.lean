import ThreeUniformDiaries.DiaryRoleEnvelopeAssembly
import ThreeUniformDiaries.DiaryTypeRespectingRangeClosure

/-!
# Native finite pointed envelopes for the diary lower bound

The manuscript's pointed envelope is a FINITE enumerated induced
hypergraph equipped with its canonical, protected-prefix inclusion.
The inclusion need not be a type-respecting map on an artificially
continued infinite tail; the relevant singleton and auxiliary meet
equalities hold only among its actual finite vertices.

This structure packages that exact finite interface, its last two
distinguished vertices, and minimality among all meet-closed carriers.
The two and three-tail constructors below discharge every field
directly from the complete V/E/S diary definition or the already
verified generic type-respecting embedding lemmas.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- A finite pointed envelope over the full prefix `j`, with the
ordered endpoints `a,b` in its last two positions. All meet claims
are restricted to the first `size` vertices of the induced graph. -/
structure FinitePointedEnvelope
    (K : Ordered3Graph Nat) (j a b : Nat) where
  size : Nat
  enumerate : Nat → Nat
  strictMono : StrictMono enumerate
  protected_prefix : ∀ t, t < j → enumerate t = t
  size_lower : j + 2 ≤ size
  size_upper : size ≤ j + 3
  first_endpoint : enumerate (size - 2) = a
  second_endpoint : enumerate (size - 1) = b
  singleton_meets :
    ∀ u v, u < size → v < size →
      K.oneMeetLevel (enumerate u) (enumerate v) =
        enumerate ((K.pullback enumerate).oneMeetLevel u v)
  auxiliary_meets :
    ∀ u v x y, u < v → x < y → v < size → y < size →
      K.auxMeetLevel (enumerate u) (enumerate v)
          (enumerate x) (enumerate y) =
        enumerate ((K.pullback enumerate).auxMeetLevel u v x y)
  minimal :
    K.IsMinimalMeetEnvelope j a b (K.selectedCarrier enumerate size)

namespace FinitePointedEnvelope

variable {K : Ordered3Graph Nat} {j a b : Nat}

/-- The actual enumerated hypergraph on the finite initial segment. -/
def induced (E : FinitePointedEnvelope K j a b) : Ordered3Graph Nat :=
  K.pullback E.enumerate

/-- Every pointed diary envelope has precisely two or three vertices
outside its protected full prefix. -/
theorem size_cases (E : FinitePointedEnvelope K j a b) :
    E.size = j + 2 ∨ E.size = j + 3 := by
  omega

/-- A pointed envelope lies in every competing type-respecting image
containing the protected prefix and both distinguished endpoints. -/
theorem subset_typeRespecting_image
    (E : FinitePointedEnvelope K j a b)
    {L : Ordered3Graph Nat}
    (φ : Embedding L K) (hφ : φ.TypeRespecting)
    (hprefix : ∀ t < j, t ∈ Set.range φ.toFun)
    (ha : a ∈ Set.range φ.toFun)
    (hb : b ∈ Set.range φ.toFun) :
    K.selectedCarrier E.enumerate E.size ⊆ Set.range φ.toFun :=
  K.minimalMeetEnvelope_subset_typeRespecting_range
    j a b (K.selectedCarrier E.enumerate E.size)
    E.minimal φ hφ hprefix ha hb

/-- A source pair separating before the cut gives a genuine finite
two-tail pointed envelope in every gappy type-respecting target. -/
def ofTwoTail
    {H : Ordered3Graph Nat}
    (ψ : Embedding H K) (hψ : ψ.TypeRespecting)
    (i u v : Nat) (hearly : H.oneMeetLevel u v < i)
    (hiu : i ≤ u) (huv : u < v) :
    FinitePointedEnvelope K (ψ i) (ψ u) (ψ v) := by
  let n := ψ i
  let f := twoTailInsertion n (ψ u) (ψ v)
  have hf : StrictMono f :=
    twoTailInsertion_strictMono n (ψ u) (ψ v)
      (ψ.strictMono.monotone hiu) (ψ.strictMono huv)
  have hfix : ∀ t, t < n → f t = t := by
    intro t ht
    exact twoTailInsertion_fix_prefix n (ψ u) (ψ v) t ht
  have hfirst : f n = ψ u := twoTailInsertion_first n (ψ u) (ψ v)
  have hsecond : f (n + 1) = ψ v :=
    twoTailInsertion_second n (ψ u) (ψ v)
  obtain ⟨hone, haux⟩ :=
    K.two_tail_ATR_after_type_embedding ψ hψ i u v
      hearly f hf hfix hfirst hsecond
  have hmin : K.IsMinimalMeetEnvelope (ψ i) (ψ u) (ψ v)
      (K.selectedCarrier f (n + 2)) :=
    K.two_tail_minimalMeetEnvelope_after_type_embedding
      ψ hψ i u v hearly f hf hfix hfirst hsecond
  refine {
    size := n + 2
    enumerate := f
    strictMono := hf
    protected_prefix := hfix
    size_lower := by omega
    size_upper := by omega
    first_endpoint := ?_
    second_endpoint := ?_
    singleton_meets := hone
    auxiliary_meets := haux
    minimal := hmin
  }
  · have hn : n + 2 - 2 = n := by omega
    rw [hn]
    exact hfirst
  · have hn : n + 2 - 1 = n + 1 := by omega
    rw [hn]
    exact hsecond

/-- A diary leaf pair whose singleton meet is at/after the cut
gives a genuine finite three-tail pointed envelope. Its split
and marker edges are obtained from the full V/E/S diary axioms. -/
def ofRoleThreeTail
    {H : Ordered3Graph Nat}
    (D : DiaryLeafPriority.RoleDiary H)
    (ψ : Embedding H K) (hψ : ψ.TypeRespecting)
    (i u v : Nat) (hi : 3 ≤ i) (hiu : i ≤ u) (huv : u < v)
    (hu : DiaryLeafPriority.IsLeaf H u)
    (hv : DiaryLeafPriority.IsLeaf H v)
    (hcase : i ≤ H.oneMeetLevel u v) :
    FinitePointedEnvelope K (ψ i) (ψ u) (ψ v) := by
  let m := H.oneMeetLevel u v
  let n := ψ i
  let f := threeTailInsertion n (ψ m) (ψ u) (ψ v)
  have hm : DiaryLeafPriority.IsOneSplit H m :=
    D.singleton_meets u v hu hv (ne_of_lt huv)
  have hmu : m < u :=
    D.leaf_meet_lt_first u v hu hv (ne_of_lt huv)
  have hf : StrictMono f :=
    threeTailInsertion_strictMono n (ψ m) (ψ u) (ψ v)
      (ψ.strictMono.monotone hcase)
      (ψ.strictMono hmu) (ψ.strictMono huv)
  have hfix : ∀ t, t < n → f t = t := by
    intro t ht
    exact threeTailInsertion_fix_prefix n (ψ m) (ψ u) (ψ v) t ht
  have hsplit : f n = ψ m :=
    threeTailInsertion_split n (ψ m) (ψ u) (ψ v)
  have hfirst : f (n + 1) = ψ u :=
    threeTailInsertion_first n (ψ m) (ψ u) (ψ v)
  have hsecond : f (n + 2) = ψ v :=
    threeTailInsertion_second n (ψ m) (ψ u) (ψ v)
  obtain ⟨hone, haux⟩ :=
    DiaryLeafPriority.oneSplit_three_tail_ATR_after_type_embedding
      D.splitEdgeShape ψ hψ i m u v hi hcase hm hu hv
      huv hmu rfl f hf hfix hsplit hfirst hsecond
  have hmin : K.IsMinimalMeetEnvelope (ψ i) (ψ u) (ψ v)
      (K.selectedCarrier f (n + 3)) :=
    K.role_three_tail_minimalMeetEnvelope_after_type_embedding
      D.splitEdgeShape ψ hψ i m u v
      hi hcase hm hu hv huv hmu rfl
      f hf hfix hsplit hfirst hsecond
  refine {
    size := n + 3
    enumerate := f
    strictMono := hf
    protected_prefix := hfix
    size_lower := by omega
    size_upper := by omega
    first_endpoint := ?_
    second_endpoint := ?_
    singleton_meets := hone
    auxiliary_meets := haux
    minimal := hmin
  }
  · have hn : n + 3 - 2 = n + 1 := by omega
    rw [hn]
    exact hfirst
  · have hn : n + 3 - 1 = n + 2 := by omega
    rw [hn]
    exact hsecond

/-- No independent marker or finite enumeration axiom is required
to construct the pointed envelope for a pair of diary leaves. -/
theorem exists_of_role_diary
    {H : Ordered3Graph Nat}
    (D : DiaryLeafPriority.RoleDiary H)
    (ψ : Embedding H K) (hψ : ψ.TypeRespecting)
    (i u v : Nat) (hi : 3 ≤ i) (hiu : i ≤ u) (huv : u < v)
    (hu : DiaryLeafPriority.IsLeaf H u)
    (hv : DiaryLeafPriority.IsLeaf H v) :
    Nonempty (FinitePointedEnvelope K (ψ i) (ψ u) (ψ v)) := by
  by_cases hearly : H.oneMeetLevel u v < i
  · exact ⟨ofTwoTail ψ hψ i u v hearly hiu huv⟩
  · have hcase : i ≤ H.oneMeetLevel u v := Nat.le_of_not_gt hearly
    exact ⟨ofRoleThreeTail D ψ hψ i u v hi hiu huv hu hv hcase⟩

end FinitePointedEnvelope
end Ordered3Graph
end ThreeUniformDiaries
