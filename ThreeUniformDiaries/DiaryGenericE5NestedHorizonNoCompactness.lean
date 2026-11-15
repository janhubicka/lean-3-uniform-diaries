import ThreeUniformDiaries.DiaryGenericE5PatternFibreCopy
import ThreeUniformDiaries.DiaryTailConePersistenceCounterexample

/-!
# Track D: even WHOLE nested generic old-E5 cones do not give a persistent image

Adversarial proof of the sharp quantifier obstruction to a tempting
countable diary-unavoidability argument.

Fix an ACTUAL enumerated generic 3-uniform hypergraph G, a finite
protected old vertex set A and a fixed prescribed Boolean old-pair
pattern q. At every natural continuation horizon N define
`GenericOldPairHorizonTail G A q N` as the vertices v>N realizing
that SAME old-pair E5 pattern against A.

The previously kernel-verified whole old-pair fibre theorem produces
an entire increasing INDUCED generic G selfcopy inside EACH such
horizon fibre. The fibres are nested in decreasing order, so they
have not merely finite-intersection nonemptiness but a WHOLE
induced generic copy in EVERY finite intersection.

Nevertheless NO fixed vertex belongs to all horizon fibres:
at horizon N=v one would need v<v. No finite palette of candidate
vertices hits every horizon either, even while each fibre is
generically rich and realizes exactly the SAME E5 old-pair pattern.

This is an ACTUAL counterexample INSIDE the ordinary generic leaf
hypergraph to the abstract inference from a nested family of full
generic cones to a persistent point. It is deliberately NOT a
counterexample involving actual full RoleDiary S1/S2/E2/E3
candidate/reserved witnesses. No diary unavoidability conclusion
or target order-monotonicity premise is asserted.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- One fixed complete old-pair E5 pattern q, with the additional
horizon-dependent LOWER bound N<v. The pattern itself never changes
with N; only the numerical tail cutoff moves. -/
def GenericOldPairHorizonTail
    (G : GenericEnumerated3Graph)
    (A : Finset Nat) (q : Nat → Nat → Bool)
    (N v : Nat) : Prop :=
  N < v ∧
    ∀ a b : Nat, a ∈ A → b ∈ A → a < b →
      (G.graph.edge a b v ↔ q a b = true)

/-- The allowed sets decrease with horizon while keeping exactly
the same old E5 pair mask. -/
theorem generic_oldPairHorizonTail_antitone
    (G : GenericEnumerated3Graph)
    (A : Finset Nat) (q : Nat → Nat → Bool)
    {N M v : Nat} (hNM : N ≤ M)
    (h : GenericOldPairHorizonTail G A q M v) :
    GenericOldPairHorizonTail G A q N v := by
  exact ⟨lt_of_le_of_lt hNM h.1, h.2⟩

/-- At EVERY source horizon N, the allowed tail contains a
COMPLETE increasing induced copy of G, preserving ALL edge and
nonedge triples of the selected copy and ONE source-independent
fixed old-pair E5 pattern q. This is a genuine geometric fact
about the actual enumerated generic hypergraph. -/
theorem GenericEnumerated3Graph.exists_induced_generic_copy_in_oldPair_horizon_tail
    (G : GenericEnumerated3Graph)
    (A : Finset Nat) (q : Nat → Nat → Bool)
    (N : Nat) :
    ∃ u : Ordered3Graph.Embedding G.graph G.graph,
      ∀ i : Nat, GenericOldPairHorizonTail G A q N (u i) := by
  obtain ⟨u, hLate, _hA, hPattern⟩ :=
    G.exists_induced_generic_selfcopy_in_oldPair_fibre A q N
  refine ⟨u, ?_⟩
  intro i
  exact ⟨hLate i, fun a b ha hb hab =>
    hPattern i a b ha hb hab⟩

/-- In fact, EACH finite intersection of horizon fibres contains
an entire induced generic copy: choose one copy above the LARGEST
horizon N and use the descending-tail property for all n≤N. -/
theorem GenericEnumerated3Graph.every_finite_horizon_intersection_contains_generic_copy
    (G : GenericEnumerated3Graph)
    (A : Finset Nat) (q : Nat → Nat → Bool)
    (N : Nat) :
    ∃ u : Ordered3Graph.Embedding G.graph G.graph,
      ∀ n : Nat, n ≤ N →
        ∀ i : Nat, GenericOldPairHorizonTail G A q n (u i) := by
  obtain ⟨u, hIn⟩ :=
    G.exists_induced_generic_copy_in_oldPair_horizon_tail A q N
  refine ⟨u, ?_⟩
  intro n hn i
  exact generic_oldPairHorizonTail_antitone G A q hn (hIn i)

/-- Even though every finite intersection contains a WHOLE
induced generic copy, there is no single image v lying in
every horizon tail. No full diary Stage is involved here. -/
theorem generic_oldPairHorizonTail_no_persistent_image
    (G : GenericEnumerated3Graph)
    (A : Finset Nat) (q : Nat → Nat → Bool) :
    ¬ ∃ v : Nat, ∀ N : Nat,
      GenericOldPairHorizonTail G A q N v := by
  rintro ⟨v, hv⟩
  exact (Nat.lt_irrefl v) (hv v).1

/-- Stronger: NO fixed FINITE palette W of candidate vertices can
meet ALL the horizon tails. Choose a horizon at least the supremum
of W. At that horizon every v∈W is TOO SMALL, although that
horizon fibre still contains a whole induced generic copy. -/
theorem generic_oldPairHorizonTail_no_finite_palette
    (G : GenericEnumerated3Graph)
    (A : Finset Nat) (q : Nat → Nat → Bool) :
    ¬ ∃ W : Finset Nat,
      ∀ N : Nat, ∃ v : Nat,
        v ∈ W ∧ GenericOldPairHorizonTail G A q N v := by
  rintro ⟨W, hAll⟩
  obtain ⟨v, hvW, hTail⟩ :=
    hAll (W.sup (fun t : Nat => t))
  have hBound : v ≤ W.sup (fun t : Nat => t) :=
    Finset.le_sup (f := fun t : Nat => t) hvW
  exact (not_lt_of_ge hBound) hTail.1

end DiaryLeafPriority
end ThreeUniformDiaries
