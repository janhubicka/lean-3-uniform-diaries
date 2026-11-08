import ThreeUniformDiaries.DiaryFiniteSingletonColour
import ThreeUniformDiaries.DiaryGenericExistenceByPairCode

/-!
# Track D adversarial regression: a coherent complete mixed type can be omitted

The complete mixed singleton-type masks below all finite target cuts
are NOT automatically realized by a single vertex, even in a genuinely
generic 3-uniform hypergraph.

Take the coherent family of masks requiring EVERY increasing pair of
earlier testing vertices to form a hyperedge with the prospective new
vertex. The finite generic extension property realizes each finite
mask by arbitrarily late vertices. But no single vertex can realize
ALL cuts when the ambient ternary edge relation is supported only
on strictly increasing triples: at cut v+2 the pair (v,v+1)
requires the impossible edge (v,v+1,v).

The explicit pair-coded canonical generic 3-graph has both properties.
Thus a virtual infinite mixed singleton type, even one finitely
realizable cofinally INSIDE A GENERIC HYPERGRAPH, need not have a
realizing vertex. This is a regression against any inference from
finite type compactness to the persistent next-leaf choice missing in
countable diary unavoidability.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The complete finite singleton mask requiring an edge at EVERY
strictly increasing pair below B (and false at non-increasing pairs). -/
def allPositiveMixedSingletonMask (B : Nat) :
    Fin B → Fin B → Bool :=
  fun x y => decide (x.val < y.val)

/-- The all-positive finite mixed masks form a coherent family:
the cut B+1 mask restricts exactly to the cut B mask. -/
theorem allPositiveMixedSingletonMask_project
    (B : Nat) (x y : Fin B) :
    allPositiveMixedSingletonMask (B + 1) x.castSucc y.castSucc =
      allPositiveMixedSingletonMask B x y := by
  simp [allPositiveMixedSingletonMask]

/-- The genuinely generic finite extension axiom realizes the
ALL-POSITIVE mixed mask below any cut B by vertices of arbitrarily
large target index. This is an ACTUAL 3-hypergraph result, not
an abstract finite-colour toy example. -/
theorem generic_allPositiveMixedSingletonMask_cofinally_realized
    (G : GenericEnumerated3Graph) (B M : Nat) :
    ∃ v : Nat, M < v ∧
      DiaryLowerBoundColors.singletonColour G.graph B v =
        allPositiveMixedSingletonMask B := by
  classical
  let m := max B (M + 1)
  obtain ⟨v, hvm, hPattern⟩ :=
    G.extension m (allPositiveMixedSingletonMask m)
  have hMv : M < v := by
    have hm : M + 1 ≤ m := le_max_right B (M + 1)
    omega
  refine ⟨v, hMv, ?_⟩
  funext x y
  by_cases hxy : x.val < y.val
  · have hx : x.val < m :=
      lt_of_lt_of_le x.isLt (le_max_left B (M + 1))
    have hy : y.val < m :=
      lt_of_lt_of_le y.isLt (le_max_left B (M + 1))
    let xx : Fin m := ⟨x.val, hx⟩
    let yy : Fin m := ⟨y.val, hy⟩
    have hxy' : xx < yy := hxy
    have hPositive : allPositiveMixedSingletonMask m xx yy = true := by
      simp [allPositiveMixedSingletonMask, hxy]
    have hEdge : G.graph.edge x.val y.val v :=
      (hPattern xx yy hxy').mpr hPositive
    simp [DiaryLowerBoundColors.singletonColour,
      allPositiveMixedSingletonMask, hxy, hEdge]
  · simp [DiaryLowerBoundColors.singletonColour,
      allPositiveMixedSingletonMask, hxy]

/-- If an ordered ternary edge predicate is supported on increasing
triples, no actual vertex realizes the entire coherent all-positive
mixed singleton type. The pair (v,v+1) at cut v+2 rules out v. -/
theorem allPositiveMixedSingletonMask_no_realizer
    (K : Ordered3Graph Nat)
    (hOrdered : ∀ a b c : Nat, K.edge a b c → b < c) :
    ¬ ∃ v : Nat, ∀ B : Nat,
      DiaryLowerBoundColors.singletonColour K B v =
        allPositiveMixedSingletonMask B := by
  rintro ⟨v, hAll⟩
  let B := v + 2
  let x : Fin B := ⟨v, by dsimp [B]; omega⟩
  let y : Fin B := ⟨v + 1, by dsimp [B]; omega⟩
  have hPos : allPositiveMixedSingletonMask B x y = true := by
    simp [allPositiveMixedSingletonMask, x, y]
  have hBit :
      DiaryLowerBoundColors.singletonColour K B v x y = true :=
    (congrFun (congrFun (hAll B) x) y).trans hPos
  have hEdge : K.edge v (v + 1) v := by
    simpa [DiaryLowerBoundColors.singletonColour, B, x, y] using hBit
  have hImpossible : v + 1 < v := hOrdered v (v + 1) v hEdge
  omega

/-- The EXPLICIT enumerated generic 3-graph simultaneously has
cofinal realizations of every finite prefix of this type and NO
vertex realizing its complete countable type. Genericity alone
cannot replace the missing realization theorem for diary tails. -/
theorem canonical_generic_has_omitted_cofinal_mixed_singleton_type :
    (∀ B M : Nat, ∃ v : Nat, M < v ∧
      DiaryLowerBoundColors.singletonColour
        canonicalGenericEnumerated3Graph.graph B v =
          allPositiveMixedSingletonMask B) ∧
    (¬ ∃ v : Nat, ∀ B : Nat,
      DiaryLowerBoundColors.singletonColour
        canonicalGenericEnumerated3Graph.graph B v =
          allPositiveMixedSingletonMask B) := by
  refine ⟨generic_allPositiveMixedSingletonMask_cofinally_realized
    canonicalGenericEnumerated3Graph, ?_⟩
  apply allPositiveMixedSingletonMask_no_realizer
  intro a b c he
  change pairCodedGenericEdge a b c at he
  exact he.2.1

end DiaryLeafPriority
end ThreeUniformDiaries
