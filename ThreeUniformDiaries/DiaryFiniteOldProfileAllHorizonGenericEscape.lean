import ThreeUniformDiaries.DiaryAllHorizonGenericOldSupportEscape
import ThreeUniformDiaries.DiaryTwoParameterFiniteOldSupportChoice

/-!
# Track A: NONVACUOUS all-horizon escape from any finite old profile palette

English-first adversarial proof: 3-uniform-diaries PR #354.

For two genuine earlier selected source leaves a<b<m, and any
FINITE set W of complete old-supported image profiles S_m→Nat,
choose a numerical B larger than EVERY p(b) for p in W.

The already kernel-checked Track D ALL-HORIZON old-support drift
theorem produces ONE unordered induced generic target leaf copy J
beyond any target cutoff M, with genuine reserved source stages
at EVERY future horizon whose NEW leaf image lies in J. It also
says EVERY such stage g must satisfy B ≤ g(b).

Consequently NO such stage may have restriction to old support
S_m in W. This is an exact obstruction to a finite old-profile
palette hitting ALL arbitrary UNORDERED generic refinements,
not to choosing a palette and selected copy JOINTLY. There are
genuine finite-horizon witnesses in the chosen J, so the no-go
does not rely on vacuous absence of reserved stages.

It does NOT rule out a selected aux-type-respecting refinement
or a geometric source-compatible pruned subsystem, and does
not refute countable diary unavoidability. Neither an anchored
generic-rich colour nor a persistent fixed new image is proved.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Any prescribed finite collection of literal old-support
profiles can be uniformly avoided, at EVERY future source horizon,
by ONE genuine induced generic leaf subcopy inside the ORIGINAL
unordered F range. Still, each horizon has genuine reserved
new-leaf stages with their new images in this same subcopy.

The source has two selected earlier genuine leaves a<b<m. The
adversarial subcopy J is chosen after the finite W but BEFORE
the horizon N and BEFORE any candidate old supported map g.
The old-support restriction of every such g is outside W.

This does not assert existence of ONE J working for all finite W,
nor an aux-type-respecting generic refinement or a coherent
countable diary embedding. -/
theorem RoleDiary.exists_generic_refinement_escaping_finite_old_profiles_all_horizons
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
    (W : Finset
      ({u : Nat // u ∈ countableDiaryFiniteSupport H m} → Nat))
    (M : Nat) :
    ∃ J : Ordered3Graph.UnorderedEmbedding G.graph K,
      (∀ t : Nat, M < J t ∧ IsLeaf K (J t) ∧
        ∃ i : Nat, J t = F i) ∧
      (∀ N : Nat,
        ∃ g : Nat → Nat,
          ReservedDiaryStage H K (fun t : Nat => F t)
            (m + 1 + N) g ∧
          ∃ t : Nat, g m = J t) ∧
      (∀ N : Nat, ∀ g : Nat → Nat,
        ReservedDiaryStage H K (fun t : Nat => F t)
          (m + 1 + N) g →
        ∀ t : Nat, g m = J t →
          (fun u : {u : Nat //
            u ∈ countableDiaryFiniteSupport H m} =>
            g u.val) ∉ W) := by
  classical
  have hbOld : b ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H m) b hb
  let T := {u : Nat // u ∈ countableDiaryFiniteSupport H m}
  let B : Nat := W.sup
    (fun p : T → Nat => p ⟨b, hbOld⟩) + 1
  obtain ⟨J, hRange, hExist, hDrift⟩ :=
    DH.exists_refinement_forcing_old_escape_at_all_finite_horizons
      DK G F hFLeaf hm ha hb hab B M
  refine ⟨J, ?_, ?_, ?_⟩
  · exact hRange
  · intro N
    obtain ⟨g, Q, t, hAtM, _hB⟩ := hExist N
    exact ⟨g, Q, t, hAtM⟩
  · intro N g Q t hAtM hProfile
    have hB : B ≤ g b := hDrift N g Q t hAtM
    have hSmall : g b ≤
        W.sup (fun p : T → Nat => p ⟨b, hbOld⟩) := by
      exact Finset.le_sup
        (f := fun p : T → Nat => p ⟨b, hbOld⟩)
        hProfile
    dsimp [B] at hB
    omega

end DiaryLeafPriority
end ThreeUniformDiaries
