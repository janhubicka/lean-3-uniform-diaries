import ThreeUniformDiaries.DiaryGenericE5PatternFibreCopy
import ThreeUniformDiaries.DiaryFiniteUniversalLeafRange
import ThreeUniformDiaries.DiarySingletonColourCofinalCone

/-!
# Track C: an induced generic old-E5 fibre in the ORIGINAL target leaf range

English proof and adversarial audit:
  janhubicka/3-uniform-diaries PR #299

A finite old-pair pattern q on actual source G vertices is realized
by one entire strictly increasing induced generic selfembedding u of
G. Compose u with ANY original UNORDERED induced embedding F:G→K
whose image consists of genuine target leaves.

Even if F reverses arbitrary index orders, F∘u is still a genuine
UNORDERED induced embedding, preserving ALL internal edges/nonedges.
Injectivity of F permits choosing u far enough out that the entire
target copy is beyond an arbitrary target numerical bound M and
beyond all protected old target images F[A].

The old-pair/new-leaf incidences are transported through the true
unordered edge predicate, without assuming F is increasing.
No full diary S1/S2/E2/E3 or next-leaf persistence is claimed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Every finite old E5 bit pattern on an actual finite old set
A of generic SOURCE indices has one induced generic leaf-copy
reservoir in the ORIGINAL unordered target prescribed range F[G],
with the entire new reservoir above an arbitrary numerical bound
and above ALL old target vertices F[A].

The whole reservoir's new vertices simultaneously realize every
prescribed old-pair/new-leaf positive/negative bit; the old pair
itself need not have increasing source and target orders aligned.
Target bits are therefore stated using unorderedEdge. -/
theorem exists_generic_leaf_subcopy_in_prescribed_oldE5_fibre
    (G : GenericEnumerated3Graph) (K : Ordered3Graph Nat)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hLeaves : ∀ n : Nat, IsLeaf K (F n))
    (A : Finset Nat) (q : Nat → Nat → Bool)
    (M : Nat) :
    ∃ J : Ordered3Graph.UnorderedEmbedding G.graph K,
      (∀ n : Nat, M < J n ∧ IsLeaf K (J n) ∧
        ∃ t : Nat, J n = F t) ∧
      (∀ n : Nat, ∀ a : Nat, a ∈ A → F a < J n) ∧
      (∀ n a b : Nat, a ∈ A → b ∈ A → a < b →
        (K.unorderedEdge (F a) (F b) (J n) ↔ q a b = true)) := by
  classical
  let T : Nat := max M (A.sup F)
  obtain ⟨N, hEventually⟩ :=
    injective_nat_eventually_above_bound F F.injective T
  obtain ⟨u, hN, hAfterOld, hPattern⟩ :=
    _root_.ThreeUniformDiaries.DiaryLeafPriority.GenericEnumerated3Graph.exists_induced_generic_selfcopy_in_oldPair_fibre G A q N
  let J : Ordered3Graph.UnorderedEmbedding G.graph K := {
    toFun := fun n => F (u n)
    injective := F.injective.comp u.strictMono.injective
    edge_iff := by
      intro a b c hab hbc
      calc
        G.graph.unorderedEdge a b c ↔ G.graph.edge a b c :=
          G.graph.unorderedEdge_iff_of_lt a b c hab hbc
        _ ↔ G.graph.edge (u a) (u b) (u c) :=
          u.edge_iff hab hbc
        _ ↔ G.graph.unorderedEdge (u a) (u b) (u c) :=
          (G.graph.unorderedEdge_iff_of_lt
            (u a) (u b) (u c)
            (u.strictMono hab) (u.strictMono hbc)).symm
        _ ↔ K.unorderedEdge (F (u a)) (F (u b)) (F (u c)) :=
          F.edge_iff (u a) (u b) (u c)
            (u.strictMono hab) (u.strictMono hbc)
  }
  have hHigh (n : Nat) : T < J n :=
    hEventually (u n) (le_of_lt (hN n))
  refine ⟨J, ?_, ?_, ?_⟩
  · intro n
    have hMT : M ≤ T := le_max_left _ _
    exact ⟨lt_of_le_of_lt hMT (hHigh n), hLeaves (u n),
      u n, rfl⟩
  · intro n a ha
    have hOldBound : F a ≤ T :=
      (Finset.le_sup (f := F) ha).trans (le_max_right _ _)
    exact lt_of_le_of_lt hOldBound (hHigh n)
  · intro n a b ha hb hab
    have hbNew : b < u n := hAfterOld n b hb
    have hSource :
        G.graph.unorderedEdge a b (u n) ↔ q a b = true := by
      calc
        G.graph.unorderedEdge a b (u n) ↔
            G.graph.edge a b (u n) :=
          G.graph.unorderedEdge_iff_of_lt a b (u n) hab hbNew
        _ ↔ q a b = true := hPattern n a b ha hb hab
    have hTarget :=
      F.edge_iff a b (u n) hab hbNew
    exact hTarget.symm.trans hSource

end DiaryLeafPriority
end ThreeUniformDiaries
