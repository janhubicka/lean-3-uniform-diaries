import ThreeUniformDiaries.DiaryGenericOldE5TargetLeafRange
import ThreeUniformDiaries.DiaryFiniteRootGenericMeetProfile

/-!
# Track C: one cofinal generic reservoir in a finite E5 fibre and S1 profile

English proof and adversarial scope:
  janhubicka/3-uniform-diaries PRs #298 and #299

Two positive ingredients can be composed WITHOUT assuming that the
prescribed unordered target generic leaf map F preserves enumeration.

First, every arbitrary finite old-source-pair E5 incidence pattern q
contains one genuinely induced generic target leaf subcopy J[G] inside
the ORIGINAL prescribed range F[G]. Second, within that actual induced
generic leaf subcopy, finite singleton ATR indivisibility produces ONE
simultaneous numeric S1 meet profile with every root of a fixed finite
set W, supporting induced generic selfcopies beyond ALL target bounds.

Important: the resulting S1 profile is EXISTENTIAL, not the profile
of an independently prescribed old diary stage. No E2/E3 marker/split
incidences, exact S2 table, source-required numeric gap, persistent
next-leaf image, or countable diary unavoidability is constructed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Inside every prescribed unordered induced generic true-leaf range,
there exists one induced generic E5-compatible subcopy J[G] such that
the original prescribed finite old-pair edge/nonedge pattern is realized
by EVERY selected leaf of J. Moreover, ONE simultaneous numerical
S1 meet profile with an arbitrary finite family of genuine target
root leaves W is cofinally supported by generic subcopies of J.

All of J[G] lies above M and after every protected original target
vertex F[A]. The selfcopies at different numerical cutoffs may differ.

The target diary S1 roles are genuine, but the chosen profile is not
asserted equal to any source-prescribed meet record. -/
theorem RoleDiary.exists_uniform_finiteRoot_generic_oldE5_reservoir
    {K : Ordered3Graph Nat} (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ n : Nat, IsLeaf K (F n))
    (A : Finset Nat) (q : Nat → Nat → Bool)
    (W : Finset Nat) (hRoots : ∀ w : Nat, w ∈ W → IsLeaf K w)
    (M : Nat) :
    ∃ J : Ordered3Graph.UnorderedEmbedding G.graph K,
      (∀ n : Nat, M < J n ∧ IsLeaf K (J n) ∧
        ∃ t : Nat, J n = F t) ∧
      (∀ n a : Nat, a ∈ A → F a < J n) ∧
      (∀ n a b : Nat, a ∈ A → b ∈ A → a < b →
        (K.unorderedEdge (F a) (F b) (J n) ↔ q a b = true)) ∧
      ∃ p : FiniteRootMeetProfile W,
        (∀ w : {w : Nat // w ∈ W},
          IsOneSplit K (p w).val ∧ (p w).val < w.val) ∧
        (∀ B : Nat,
          ∃ (u : Ordered3Graph.Embedding G.graph G.graph),
            u.AuxTypeRespecting ∧
            ∀ t : Nat,
              B < J (u t) ∧
              (∀ w : {w : Nat // w ∈ W},
                K.oneMeetLevel w.val (J (u t)) = (p w).val)) := by
  obtain ⟨J, hRange, hAboveOld, hOldPattern⟩ :=
    exists_generic_leaf_subcopy_in_prescribed_oldE5_fibre
      G K F hFLeaf A q M
  have hJLeaves : ∀ t : Nat, IsLeaf K (J t) := by
    intro t
    exact (hRange t).2.1
  obtain ⟨p, hRoles, hGenericAtEveryCut⟩ :=
    DK.exists_uniform_finiteRootMeet_generic_subcopies
      G J hJLeaves W hRoots
  exact ⟨J, hRange, hAboveOld, hOldPattern,
    p, hRoles, hGenericAtEveryCut⟩

end DiaryLeafPriority
end ThreeUniformDiaries
