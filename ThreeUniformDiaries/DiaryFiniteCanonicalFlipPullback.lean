import ThreeUniformDiaries.DiaryFiniteTargetFlipInducedSource
import ThreeUniformDiaries.DiaryFiniteUniversalEdgeCode

/-!
# Canonical finite source flip pulled back from a target flip

The previously verified exists_inducedSourceFlip_of_targetFlip
constructs an existential bounded diary A' with its full edge
relation equal on increasing source triples to the restriction
of the target flip along the original finite embedding f.

There is actually NO CHOICE in the pulled-back graph. We give
its literal finite edge table and prove a uniqueness theorem:
every bounded finite edge frame matching these values is
definitionally the same graph as the canonical pullback.
Consequently the canonical graph itself is a genuine finite
flip of A, including its exact leaf singleton/full pair-meets.

This replaces the existential source-flip witness by a
reusable, deterministic graph expression on the original
finite ordered vertex set. Later compatibility/causality
lemmas can speak about this graph directly.

The result does NOT say f:A->B' preserves arbitrary mixed
numerical meets. It does NOT establish every-target-flip
absorption or prefix causality.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Actual induced ordered ternary pullback on the source
initial segment. All edges outside the bounded increasing
source triples are set to false. -/
def finiteDiaryPullbackGraph
    (T : Ordered3Graph Nat) (n : Nat)
    (f : Nat → Nat) : Ordered3Graph Nat where
  edge a b c :=
    a < b ∧ b < c ∧ c < n ∧ T.edge (f a) (f b) (f c)

/-- Complete induced edge-and-nonedge identity for genuine
source ordered triples, with the exact bounded source frame. -/
theorem finiteDiaryPullbackGraph_edge_iff
    (T : Ordered3Graph Nat) (n : Nat)
    (f : Nat → Nat)
    (a b c : Nat) (hab : a < b)
    (hbc : b < c) (hcn : c < n) :
    (finiteDiaryPullbackGraph T n f).edge a b c ↔
       T.edge (f a) (f b) (f c) := by
  simp only [finiteDiaryPullbackGraph, hab, hbc, hcn,
    true_and]

/-- Literal bounded support of the canonical source edges
when the finite target itself has the required edge frame and
the embedding fixes marker 2. No unconditional 3-uniform
claim is made for an arbitrary target edge relation. -/
theorem finiteDiaryPullbackGraph_frame
    (T : Ordered3Graph Nat) (n k : Nat)
    (f : Nat → Nat)
    (hn : 3 ≤ n)
    (FT : FiniteDiaryEdgeFrame T k)
    (hf2 : f 2 = 2) :
    FiniteDiaryEdgeFrame (finiteDiaryPullbackGraph T n f) n := by
  refine ⟨hn, ?_⟩
  intro a b c he
  change a < b ∧ b < c ∧ c < n ∧
    T.edge (f a) (f b) (f c) at he
  obtain ⟨hab,hbc,hcn,hT⟩ := he
  have hTarget3 : 3 ≤ f c :=
    (FT.edge_support (f a) (f b) (f c) hT).2.2.1
  have hc3 : 3 ≤ c := by
    by_contra hsmall
    have hc2 : c = 2 := by omega
    subst c
    rw [hf2] at hTarget3
    omega
  exact ⟨hab,hbc,hc3,hcn⟩

/-- A bounded finite ordered graph agreeing with the target
on all increasing source triples is precisely the canonical
pullback. In particular, no additional external edge values
or witness choices can affect the resulting source graph. -/
theorem finiteDiaryPullbackGraph_unique
    (T : Ordered3Graph Nat) (n : Nat)
    (f : Nat → Nat)
    (H : Ordered3Graph Nat) (FH : FiniteDiaryEdgeFrame H n)
    (hInduced : ∀ a b c : Nat, a < b → b < c → c < n →
      (H.edge a b c ↔ T.edge (f a) (f b) (f c))) :
    finiteDiaryPullbackGraph T n f = H := by
  apply finiteDiary_graph_ext
  intro a b c
  constructor
  · intro h
    have hab : a < b := h.1
    have hbc : b < c := h.2.1
    have hcn : c < n := h.2.2.1
    exact (hInduced a b c hab hbc hcn).mpr h.2.2.2
  · intro h
    obtain ⟨hab,hbc,_hc3,hcn⟩ :=
      FH.edge_support a b c h
    exact ⟨hab,hbc,hcn,
      (hInduced a b c hab hbc hcn).mp h⟩

/-- The source flip obtained by pulling back any finite target
flip has a uniquely determined edge relation: the canonical
induced pullback on [0,n). It is a real finite diary and a
real flip of A, with all required LEAF meets unchanged. -/
theorem finiteDiaryPullbackGraph_is_sourceFlip
    {A B B' : Ordered3Graph Nat}
    {n k : Nat} {f : Nat → Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (E : FiniteMeetEmbedding A B n f)
    (hRange : ∀ u, u < n → f u < k)
    (F : FiniteDiaryFlip B B' k) :
    FiniteDiaryFlip A (finiteDiaryPullbackGraph B' n f) n := by
  obtain ⟨H,hFlip,hEdge⟩ :=
    exists_inducedSourceFlip_of_targetFlip DA E hRange F
  have hSame : finiteDiaryPullbackGraph B' n f = H :=
    finiteDiaryPullbackGraph_unique B' n f H
      hFlip.target_diary.prediary.frame hEdge
  rw [hSame]
  exact hFlip

end DiaryLeafPriority
end ThreeUniformDiaries
