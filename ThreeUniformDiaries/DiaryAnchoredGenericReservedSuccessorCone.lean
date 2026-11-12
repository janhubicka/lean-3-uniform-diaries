import ThreeUniformDiaries.DiaryCofinalGenericFiniteColourSubcopies
import ThreeUniformDiaries.DiaryReservedTailLeafReplacement
import ThreeUniformDiaries.DiaryFiniteSingletonColour

/-!
# Track C: an anchored winning finite colour yields GENERIC reserved successors

English proof/adversarial audit:
  janhubicka/3-uniform-diaries PR #310

Fix an actual genuine RESERVED diary successor P at the new
source leaf m. A full finite mixed singleton colour cut Cut must
dominate EVERY image of a supported source coordinate OTHER
THAN m, including all new numerical S1/S2 generator rows.

If the existing new leaf g0(m) has the same complete finite colour
c as one whole cofinally generic true-leaf fibre in the ORIGINAL
prescribed unordered target leaf range F[G], then the exact verified
tail-replacement theorem upgrades EVERY vertex of those generic
subcopies into a genuine reserved immediate successor. All old
selected source leaf images remain fixed, and all edge/nonedge,
roles, numeric S1/S2 meets and future numerical reserve survive.

The winning generic colour exists by the verified finite-colour
generic-subcopy theorem, but the existence of an ANCHOR reserved
successor in THAT particular winning colour is an additional
nonemptiness condition. No later finite-horizon persistence,
source-prescribed new split profile existence or countable diary
unavoidability follows.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A full monochromatic generic cone of actual reserved immediate
successors follows from ONE real anchored reserved successor g0 whose
new-leaf mixed singleton colour is the colour of the entire cone.

The cut dominates ALL images of non-new supported vertices in
S_(m+1). Every selected target leaf lies at least as far as g0(m),
so the verified exact tail-replacement theorem applies.

The resulting successor maps fix every previously selected SOURCE
leaf. They need not be mutually compatible through any later source
horizon, and this is not an unconditional existence theorem. -/
theorem ReservedDiaryStage.generic_reserved_successor_cone_of_colour_anchor
    {H K : Ordered3Graph Nat}
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    {m Cut : Nat} (hm : IsLeaf H m)
    {g0 : Nat → Nat}
    (P : ReservedDiaryStage H K F (m + 1) g0)
    (hBelow : ∀ x : Nat,
      x ∈ countableDiaryFiniteSupport H (m + 1) →
      x ≠ m → g0 x < Cut)
    (c : Fin Cut → Fin Cut → Bool)
    (hAnchor :
      DiaryLowerBoundColors.singletonColour K Cut (g0 m) = c)
    (hCone : ∀ M : Nat,
      ∃ (u : Ordered3Graph.Embedding G.graph G.graph),
        u.AuxTypeRespecting ∧
        ∀ n : Nat,
          M < F (u n) ∧
          DiaryLowerBoundColors.singletonColour K Cut (F (u n)) = c) :
    ∀ M : Nat,
      ∃ (u : Ordered3Graph.Embedding G.graph G.graph),
        u.AuxTypeRespecting ∧
        ∀ n : Nat,
          M < F (u n) ∧ g0 m ≤ F (u n) ∧
          ReservedDiaryStage H K F (m + 1)
            (replaceAt g0 m (F (u n))) ∧
          (∀ a : Nat, a ∈ countableDiaryLeafPrefix H m →
            replaceAt g0 m (F (u n)) a = g0 a) := by
  intro M
  obtain ⟨u, hu, hAll⟩ := hCone (max M (g0 m))
  refine ⟨u, hu, ?_⟩
  intro n
  obtain ⟨hLate, hColour⟩ := hAll n
  have hEqual :
      DiaryLowerBoundColors.singletonColour K Cut (g0 m) =
        DiaryLowerBoundColors.singletonColour K Cut (F (u n)) :=
    hAnchor.trans hColour.symm
  have hTail : K.SameOneTypeBelow Cut (g0 m) (F (u n)) :=
    (DiaryLowerBoundColors.singletonColour_eq_iff
      K Cut (g0 m) (F (u n))).mp hEqual
  have hvLater : g0 m ≤ F (u n) :=
    (le_max_right M (g0 m)).trans hLate.le
  have hStage : ReservedDiaryStage H K F (m + 1)
      (replaceAt g0 m (F (u n))) :=
    ReservedDiaryStage.replace_new_leaf_of_same_tail_type
      hm P hBelow hTail hvLater (hFLeaf (u n)) ⟨u n, rfl⟩
  refine ⟨lt_of_le_of_lt (le_max_left M (g0 m)) hLate,
    hvLater, hStage, ?_⟩
  intro a ha
  have haBefore : a < m :=
    ((mem_countableDiaryLeafPrefix_iff H m a).mp ha).2.1
  exact replaceAt_other g0 m (F (u n)) a (ne_of_lt haBefore)

/-- Finite generic Ramsey always selects SOME complete mixed singleton
colour c supporting induced generic subcopies arbitrarily high in
the given unordered target true-leaf range. If a supplied actual
reserved successor's next leaf happens to have precisely THAT colour,
then entire cofinal generic cones consist of actual reserved
successors, by the preceding result.

The matching-anchor implication is explicit; it must not be
silently inferred from existence of any reserved successor or
from ordinary generic leaf-only extension. -/
theorem ReservedDiaryStage.exists_winning_colour_with_anchored_generic_consequence
    {H K : Ordered3Graph Nat}
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    {m Cut : Nat} (hm : IsLeaf H m)
    {g0 : Nat → Nat}
    (P : ReservedDiaryStage H K F (m + 1) g0)
    (hBelow : ∀ x : Nat,
      x ∈ countableDiaryFiniteSupport H (m + 1) →
      x ≠ m → g0 x < Cut) :
    ∃ c : Fin Cut → Fin Cut → Bool,
      (∀ M : Nat,
        ∃ (u : Ordered3Graph.Embedding G.graph G.graph),
          u.AuxTypeRespecting ∧
          ∀ n : Nat,
            M < F (u n) ∧
            DiaryLowerBoundColors.singletonColour K Cut (F (u n)) = c) ∧
      (DiaryLowerBoundColors.singletonColour K Cut (g0 m) = c →
        ∀ M : Nat,
          ∃ (u : Ordered3Graph.Embedding G.graph G.graph),
            u.AuxTypeRespecting ∧
            ∀ n : Nat,
              M < F (u n) ∧ g0 m ≤ F (u n) ∧
              ReservedDiaryStage H K F (m + 1)
                (replaceAt g0 m (F (u n))) ∧
              (∀ a : Nat, a ∈ countableDiaryLeafPrefix H m →
                replaceAt g0 m (F (u n)) a = g0 a)) := by
  obtain ⟨c, hCone⟩ :=
    exists_uniform_cofinal_generic_monochromatic_subcopies
      G (fun n => DiaryLowerBoundColors.singletonColour K Cut (F n))
        F F.injective
  exact ⟨c, hCone, fun hAnchor =>
    ReservedDiaryStage.generic_reserved_successor_cone_of_colour_anchor
      G F hFLeaf hm P hBelow c hAnchor hCone⟩

end DiaryLeafPriority
end ThreeUniformDiaries
