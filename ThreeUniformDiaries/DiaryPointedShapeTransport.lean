import ThreeUniformDiaries.DiaryPointedProfileFromRoles
import ThreeUniformDiaries.DiaryPointedEnvelopeShape

/-!
# Transporting diary pointed-envelope type profiles through a type-respecting embedding

The role/edge axioms determine the one-split and mixed-pair profiles
from the leaf-pair 2-type.  Type-respectingness transfers those
*ordinary* profiles across arbitrary gaps in the target enumeration.
We then compare the two induced prefix-plus-three-tail hypergraphs.

This is a conditional structural step: the role-shape axioms, the
existence of the pointed envelope as the minimal meet-closed carrier,
and the lower-bound stabilisation/fusion argument remain separate.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RolePointedEnvelopeAxioms

/-- Full 2-type equality of two ordered diary leaf pairs transfers all
five pointed-envelope profiles to the target of a type-respecting
embedding, even if the embedding skips target levels.  In particular,
no general mixed-pair auxiliary-meet preservation is assumed. -/
theorem pointed_profiles_after_type_embedding
    {H K : Ordered3Graph Nat} (D : RolePointedEnvelopeAxioms H)
    (ψ : Ordered3Graph.Embedding H K)
    (hψ : ψ.TypeRespecting)
    (i m n a b c d : Nat)
    (hi : 3 ≤ i) (him : i ≤ m) (hin : i ≤ n)
    (hm : IsOneSplit H m) (hn : IsOneSplit H n)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hab : a < b) (hcd : c < d)
    (hma : m < a) (hnc : n < c)
    (hmeetAB : H.oneMeetLevel a b = m)
    (hmeetCD : H.oneMeetLevel c d = n)
    (hpair : H.SameTwoTypeBelow i a b c d) :
    K.SameOneTypeBelow (ψ i) (ψ m) (ψ n) ∧
    K.SameTwoTypeBelow (ψ i) (ψ m) (ψ a) (ψ n) (ψ c) ∧
    K.SameTwoTypeBelow (ψ i) (ψ m) (ψ b) (ψ n) (ψ d) ∧
    K.SameTwoTypeBelow (ψ i) (ψ a) (ψ b) (ψ c) (ψ d) ∧
    (K.edge (ψ m) (ψ a) (ψ b) ↔
      K.edge (ψ n) (ψ c) (ψ d)) := by
  obtain ⟨hsplit, hmixA, hmixB, hterminal⟩ :=
    D.pointed_profiles_of_leaf_pair_type
      i m n a b c d hi him hin hm hn ha hb hc hd
      hab hcd hma hnc hmeetAB hmeetCD hpair
  have hmb : m < b := lt_trans hma hab
  have hnd : n < d := lt_trans hnc hcd
  have hsplit' : K.SameOneTypeBelow (ψ i) (ψ m) (ψ n) :=
    (hψ.one i m n him hin).mp hsplit
  have hmixA' : K.SameTwoTypeBelow (ψ i) (ψ m) (ψ a) (ψ n) (ψ c) :=
    (hψ.two i m a n c him hma hin hnc).mp hmixA
  have hmixB' : K.SameTwoTypeBelow (ψ i) (ψ m) (ψ b) (ψ n) (ψ d) :=
    (hψ.two i m b n d him hmb hin hnd).mp hmixB
  have hleaf' : K.SameTwoTypeBelow (ψ i) (ψ a) (ψ b) (ψ c) (ψ d) :=
    (hψ.two i a b c d (him.trans hma.le) hab
      (hin.trans hnc.le) hcd).mp hpair
  have hterminal' :
      K.edge (ψ m) (ψ a) (ψ b) ↔
      K.edge (ψ n) (ψ c) (ψ d) := by
    calc
      K.edge (ψ m) (ψ a) (ψ b) ↔ H.edge m a b :=
        (ψ.edge_iff hma hab).symm
      _ ↔ H.edge n c d := hterminal
      _ ↔ K.edge (ψ n) (ψ c) (ψ d) :=
        ψ.edge_iff hnc hcd
  exact ⟨hsplit', hmixA', hmixB', hleaf', hterminal'⟩

/-- Two pointed 3-tail pictures arising from same-type leaf pairs
induce identical ordered hypergraphs on their enumerated carriers.
The full prefix is retained literally, while the six exterior
vertices may lie at arbitrary gaps above the protected cut. -/
theorem pointed_three_tail_shapes_after_type_embedding
    {H K : Ordered3Graph Nat} (D : RolePointedEnvelopeAxioms H)
    (ψ : Ordered3Graph.Embedding H K)
    (hψ : ψ.TypeRespecting)
    (i m n a b c d : Nat)
    (hi : 3 ≤ i) (him : i ≤ m) (hin : i ≤ n)
    (hm : IsOneSplit H m) (hn : IsOneSplit H n)
    (ha : IsLeaf H a) (hb : IsLeaf H b)
    (hc : IsLeaf H c) (hd : IsLeaf H d)
    (hab : a < b) (hcd : c < d)
    (hma : m < a) (hnc : n < c)
    (hmeetAB : H.oneMeetLevel a b = m)
    (hmeetCD : H.oneMeetLevel c d = n)
    (hpair : H.SameTwoTypeBelow i a b c d)
    (f g : Nat → Nat)
    (hfixf : ∀ t, t < ψ i → f t = t)
    (hfixg : ∀ t, t < ψ i → g t = t)
    (hfM : f (ψ i) = ψ m)
    (hfA : f (ψ i + 1) = ψ a)
    (hfB : f (ψ i + 2) = ψ b)
    (hgN : g (ψ i) = ψ n)
    (hgC : g (ψ i + 1) = ψ c)
    (hgD : g (ψ i + 2) = ψ d)
    (x y z : Nat)
    (hxy : x < y) (hyz : y < z) (hz : z < ψ i + 3) :
    (K.pullback f).edge x y z ↔ (K.pullback g).edge x y z := by
  obtain ⟨hsplit, hmixA, hmixB, hleaf, hterminal⟩ :=
    D.pointed_profiles_after_type_embedding ψ hψ
      i m n a b c d hi him hin hm hn ha hb hc hd
      hab hcd hma hnc hmeetAB hmeetCD hpair
  have hsplitFG :
      K.SameOneTypeBelow (ψ i) (f (ψ i)) (g (ψ i)) := by
    simpa only [hfM, hgN] using hsplit
  have hleafFG :
      K.SameTwoTypeBelow (ψ i)
        (f (ψ i + 1)) (f (ψ i + 2))
        (g (ψ i + 1)) (g (ψ i + 2)) := by
    simpa only [hfA, hfB, hgC, hgD] using hleaf
  have hmixAFG :
      K.SameAuxTypeBelow (ψ i)
        (f (ψ i)) (f (ψ i + 1))
        (g (ψ i)) (g (ψ i + 1)) := by
    simpa only [hfM, hfA, hgN, hgC] using hmixA.2.2
  have hmixBFG :
      K.SameAuxTypeBelow (ψ i)
        (f (ψ i)) (f (ψ i + 2))
        (g (ψ i)) (g (ψ i + 2)) := by
    simpa only [hfM, hfB, hgN, hgD] using hmixB.2.2
  have hterminalFG :
      K.edge (f (ψ i)) (f (ψ i + 1)) (f (ψ i + 2)) ↔
      K.edge (g (ψ i)) (g (ψ i + 1)) (g (ψ i + 2)) := by
    simpa only [hfM, hfA, hfB, hgN, hgC, hgD] using hterminal
  exact K.pointed_three_tail_edge_agreement_of_pair_type
    f g (ψ i) hfixf hfixg hsplitFG hleafFG
    hmixAFG hmixBFG hterminalFG x y z hxy hyz hz

end RolePointedEnvelopeAxioms
end DiaryLeafPriority
end ThreeUniformDiaries
