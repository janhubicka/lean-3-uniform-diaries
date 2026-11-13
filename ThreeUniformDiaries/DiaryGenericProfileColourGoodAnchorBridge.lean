import ThreeUniformDiaries.DiaryGenericGoodOrBadColourCone
import ThreeUniformDiaries.DiaryOldStageE5UniformNumericGenericCone

/-!
# Track A: a good complete old-cut colour retains ALL properties of generic profile cones

English-first adversarial proof: 3-uniform-diaries PR #327.

The all-or-none reserved next-leaf old-colour theorem turns any
COFINAL FAMILY OF WHOLE monochromatic generic J-subcopies with an
additional property R into a dichotomy. Either the colour has no
compatible reserved next-leaf anchor anywhere, or those VERY SAME
arbitrarily high induced generic subcopies consist entirely of
actual reserved next-leaf images, retaining EVERY original R bit.

In particular R can be the joint source-required positive/negative
old E5 table and the SAME existentially selected complete target
S1 / both S2 numeric profiles from the verified Track A theorem.
The critical missing input is a source-compatible anchor for the
selected complete colour, not a separate intersection of E5 and
numeric-profile fibres. This theorem does not provide the anchor,
does not force genericity of a cofinal good colour, and does not
give any fixed next-leaf image surviving later source horizons.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- An induced generic leaf range J inside the ORIGINAL prescribed
F range has arbitrarily late WHOLE induced generic subcopies of ONE
old-cut colour c, all satisfying an arbitrary target property R.
Then either c is globally reserved-next-leaf-anchor-free, or for
every M there is a WHOLE induced generic subcopy inside that SAME J
whose EVERY vertex retains R and is an ACTUAL compatible reserved
immediate next-leaf image.

Neither F nor J is assumed to be increasing in target values.
The additional property R is preserved literally, so it can encode
all source-required E5 bits AND all selected full S1/S2 numeric
profiles at once. The theorem does not choose a good colour. -/
theorem generic_profile_colour_cones_good_or_no_compatible_anchor
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m : Nat}
    (hm : IsLeaf H m)
    (G : GenericEnumerated3Graph)
    (J : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hJLeaves : ∀ n : Nat, IsLeaf K (J n))
    (hJInF : ∀ n : Nat, ∃ t : Nat, J n = F t)
    (c : Fin (oldStageTailCut H m f) →
      Fin (oldStageTailCut H m f) → Bool)
    (R : Nat → Prop)
    (hProfileCones : ∀ M : Nat,
      ∃ u : Ordered3Graph.Embedding G.graph G.graph,
        u.AuxTypeRespecting ∧
        ∀ t : Nat,
          M < J (u t) ∧
          DiaryLowerBoundColors.singletonColour K
            (oldStageTailCut H m f) (J (u t)) = c ∧
          R (J (u t))) :
    (∀ v : Nat,
      HasCompatibleReservedNextLeaf H K F f m v →
      DiaryLowerBoundColors.singletonColour K
        (oldStageTailCut H m f) v ≠ c) ∨
    (∀ M : Nat,
      ∃ u : Ordered3Graph.Embedding G.graph G.graph,
        u.AuxTypeRespecting ∧
        ∀ t : Nat,
          M < J (u t) ∧
          DiaryLowerBoundColors.singletonColour K
            (oldStageTailCut H m f) (J (u t)) = c ∧
          R (J (u t)) ∧
          HasCompatibleReservedNextLeaf H K F f m (J (u t))) := by
  classical
  rcases compatible_reserved_nextLeaf_colour_fibre_all_or_none
    (H := H) (K := K) (F := F) (f := f) (m := m)
    hm c with hNone | ⟨T, hGood⟩
  · exact Or.inl hNone
  · right
    intro M
    obtain ⟨u, hu, hAll⟩ := hProfileCones (max M T)
    refine ⟨u, hu, ?_⟩
    intro t
    obtain ⟨hHigh, hColour, hR⟩ := hAll t
    have hM : M < J (u t) :=
      lt_of_le_of_lt (le_max_left M T) hHigh
    have hT : T ≤ J (u t) :=
      (le_max_right M T).trans hHigh.le
    exact ⟨hM, hColour, hR,
      hGood (J (u t)) hT (hJLeaves (u t))
        (hJInF (u t)) hColour⟩

end DiaryLeafPriority
end ThreeUniformDiaries
