import ThreeUniformDiaries.DiaryFiniteFamilyFiniteTarget

/-!
# Canonical finite Boolean encoding of bounded diary edge tables

A bounded finite diary is an ordered ternary edge relation
supported on the finite initial segment [0,n). Consequently
it is determined by a finite Boolean table on (Fin n)^3.
We prove the literal reconstruction, without assuming a diary's
split axioms or any false type-compression equivalence.

This provides a finite enumeration for the FIRST flip property:
joint embedding of every finite diary of one fixed size. It does
not assert that every flip of the common target contains a
prescribed source.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Finite Boolean table of ternary incidences in a bounded
initial segment. Non-increasing triples need not be filtered
here because the reconstructed graph enforces increasing order. -/
abbrev FiniteDiaryEdgeCode (n : Nat) :=
  Fin n → Fin n → Fin n → Bool

/-- The actual ternary edge table of any ordered graph on
the first n vertices, including the nonedges. -/
noncomputable def finiteDiaryEdgeCode
    (H : Ordered3Graph Nat) (n : Nat) :
    FiniteDiaryEdgeCode n := by
  classical
  exact fun a b c => decide (H.edge a.val b.val c.val)

/-- Interpret a Boolean table as an ordered 3-uniform relation
supported in the first n vertices and with increasing edges. -/
noncomputable def finiteDiaryCodeGraph
    (n : Nat) (code : FiniteDiaryEdgeCode n) :
    Ordered3Graph Nat where
  edge a b c :=
    ∃ (ha : a < n) (hb : b < n) (hc : c < n),
      a < b ∧ b < c ∧
      code ⟨a,ha⟩ ⟨b,hb⟩ ⟨c,hc⟩ = true

/-- Every bounded ordered graph is reconstructed *literally*
from its Boolean incidence table, edges AND nonedges. -/
theorem finiteDiaryCodeGraph_edge_iff
    (H : Ordered3Graph Nat) (n : Nat)
    (F : FiniteDiaryEdgeFrame H n)
    (a b c : Nat) :
    (finiteDiaryCodeGraph n (finiteDiaryEdgeCode H n)).edge a b c ↔
      H.edge a b c := by
  classical
  constructor
  · intro he
    rcases he with ⟨ha,hb,hc,hab,hbc,hbit⟩
    change decide (H.edge a b c) = true at hbit
    simpa only [decide_eq_true_eq] using hbit
  · intro he
    obtain ⟨hab,hbc,_hc3,hcn⟩ := F.edge_support a b c he
    have han : a < n := by omega
    have hbn : b < n := by omega
    refine ⟨han,hbn,hcn,hab,hbc,?_⟩
    change decide (H.edge a b c) = true
    simp only [decide_eq_true_eq]
    exact he

/-- Structural extensionality for ordered ternary relations.
The relation is the only field of Ordered3Graph. -/
theorem finiteDiary_graph_ext
    {H K : Ordered3Graph Nat}
    (h : ∀ a b c : Nat, H.edge a b c ↔ K.edge a b c) :
    H = K := by
  cases H with
  | mk he =>
    cases K with
    | mk ke =>
      have hfun : he = ke := by
        funext a b c
        exact propext (h a b c)
      cases hfun
      rfl

/-- Actual equality of a finite edge frame and the graph
decoded from its own code. This is stronger than an embedding. -/
theorem finiteDiaryCodeGraph_reconstruct
    (H : Ordered3Graph Nat) (n : Nat)
    (F : FiniteDiaryEdgeFrame H n) :
    finiteDiaryCodeGraph n (finiteDiaryEdgeCode H n) = H := by
  apply finiteDiary_graph_ext
  intro a b c
  exact finiteDiaryCodeGraph_edge_iff H n F a b c

end DiaryLeafPriority
end ThreeUniformDiaries
