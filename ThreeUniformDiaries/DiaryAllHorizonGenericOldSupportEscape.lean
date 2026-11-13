import ThreeUniformDiaries.DiaryGenericRefinementForcesOldSupportEscape

/-!
# Track D: one adversarial generic refinement supports every finite source horizon

The verified all-witness old-support drift theorem supplies a genuine
unordered induced generic refinement J of the ORIGINAL F[G] range,
above any M, on which every actual reserved immediate next-leaf stage
with new image in J must place a prescribed earlier old source leaf b
at least B.

We sharpen NONVACUITY to ALL finite continuation horizons: for this
SAME J (chosen before N), the already kernel-verified independent
reserved-stage existence theorem constructs a genuine full supported
reserved map at source horizon m+1+N for EACH N, whose genuine
new-leaf image lies in J. Restrict the map to m+1 and use the
universal drift property. All finite horizons occur in one J,
and every such horizon witness has old b-image at least B.

The source witnesses may vary on ALL old support coordinates and
on the new leaf as N grows. This is NOT a common old map, a fixed
next-leaf image, a countable coherent embedding or the assertion
that the full-diary unavoidability theorem is false. It explicitly
demonstrates why independent finite-horizon existence after generic
refinement is insufficient for countable fusion.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- For EACH numerical old-support bound B and target cutoff M,
there is a SINGLE unordered induced generic target subcopy J inside
the original prescribed F range such that:

(1) every J leaf is beyond M;
(2) for EVERY finite future source horizon N, some genuine complete
    reserved S_(m+1+N) stage exists in the ORIGINAL F range whose
    new source leaf m has image J(t), with old b-image >= B;
(3) in fact ALL such horizon witnesses have old b-image >= B.

J is chosen before N, but stages g_N are independently chosen.
No compatibility among distinct g_N is asserted. -/
theorem RoleDiary.exists_refinement_forcing_old_escape_at_all_finite_horizons
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    {m a b : Nat}
    (hm : IsLeaf H m)
    (ha : a ∈ countableDiaryLeafPrefix H m)
    (hb : b ∈ countableDiaryLeafPrefix H m)
    (hab : a < b)
    (B M : Nat) :
    ∃ J : Ordered3Graph.UnorderedEmbedding G.graph K,
      (∀ t : Nat,
        M < J t ∧ IsLeaf K (J t) ∧
        ∃ i : Nat, J t = F i) ∧
      (∀ N : Nat,
        ∃ g : Nat → Nat,
          ReservedDiaryStage H K (fun t : Nat => F t)
            (m + 1 + N) g ∧
          ∃ t : Nat, g m = J t ∧ B ≤ g b) ∧
      (∀ N : Nat, ∀ g : Nat → Nat,
        ReservedDiaryStage H K (fun t : Nat => F t)
          (m + 1 + N) g →
        ∀ t : Nat, g m = J t → B ≤ g b) := by
  classical
  obtain ⟨J,hRange,hDrift⟩ :=
    exists_generic_refinement_forcing_old_support_escape
      G F hFLeaf hm ha hb hab B M
  have hUniversal : Ordered3Graph.CountablyUniversal G.graph := by
    intro A
    obtain ⟨v,hMono,hInduced⟩ :=
      G.exists_countable_induced_embedding A
    let e : Ordered3Graph.Embedding A G.graph := {
      toFun := v
      strictMono := hMono
      edge_iff := by
        intro x y z hxy hyz
        exact hInduced x y z hxy hyz
    }
    exact ⟨e.asUnordered⟩
  have hJLeaf (t : Nat) : IsLeaf K (J t) :=
    (hRange t).2.1
  have hJInsideF (t : Nat) : ∃ i : Nat, J t = F i :=
    (hRange t).2.2
  have hDriftAtHorizon (N : Nat) (g : Nat → Nat)
      (Q : ReservedDiaryStage H K (fun t : Nat => F t)
        (m + 1 + N) g)
      (t : Nat) (hNew : g m = J t) :
      B ≤ g b :=
    hDrift g (Q.restrict (by omega)) t hNew
  refine ⟨J,hRange,?_,hDriftAtHorizon⟩
  intro N
  obtain ⟨g,Q⟩ :=
    exists_independent_reserved_stage_in_universal_leaf_range
      DH DK G hUniversal J hJLeaf (m + 1 + N)
  have hmSelected : m ∈ countableDiaryLeafPrefix H (m + 1 + N) :=
    (mem_countableDiaryLeafPrefix_iff H (m + 1 + N) m).mpr
      ⟨hm.1,by omega,hm⟩
  have hmSupported : m ∈ countableDiaryFiniteSupport H (m + 1 + N) :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H (m + 1 + N)) m hmSelected
  obtain ⟨t,hNew⟩ := Q.1.leaf_range m hmSupported hm
  have QOriginal :
      ReservedDiaryStage H K (fun t : Nat => F t)
        (m + 1 + N) g :=
    Q.weaken_leaf_range hJInsideF
  exact ⟨g,QOriginal,t,hNew,
    hDriftAtHorizon N g QOriginal t hNew⟩

end DiaryLeafPriority
end ThreeUniformDiaries
