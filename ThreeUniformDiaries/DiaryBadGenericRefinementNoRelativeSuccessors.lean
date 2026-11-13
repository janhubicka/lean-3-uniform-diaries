import ThreeUniformDiaries.DiaryGenericBadColourSubcopies
import ThreeUniformDiaries.DiaryFiniteCandidateOldColourDichotomy

/-!
# Track A: arbitrary generic refinement can destroy ALL relative successors of a fixed stage

The merged Track A bad-colour theorem provides, for every ACTUAL
old reserved diary stage P with TWO distinct selected source
leaves and an original unordered induced GENERIC target true-leaf
copy F, an actual induced generic subcopy J in F and ONE complete
old-cut colour c such that:
  - beyond every target bound some induced generic selfcopy u
    has all J(u n) of colour c;
  - NO compatible reserved immediate successor of the fixed
    old stage has colour c.

Selecting ONE of these entire monochromatic generic selfcopies
and composing it with J produces a further genuine induced
generic subcopy U of the ORIGINAL prescribed F range above any
chosen target bound M, in which EVERY vertex is incompatible
with a reserved next-leaf extension fixing old P.

This gives a sharp impossibility theorem for the strategy
"first freeze an arbitrary old diary stage, then freely pass
to an arbitrary generic target subcopy, and expect relative
successor existence". That strategy is FALSE even though the
refined target leaf reduct is still an induced generic copy.

Under a full source RoleDiary, the exact finite candidate
criterion immediately strengthens this to exclusion of ALL
complete functional S1/S2 generator candidates with future
order reserve in the refined generic subcopy.

This does NOT rule out source-compatible JOINT selection of the
old stage and the target generic subcopy or the final diary
unavoidability theorem. It is a structural obstruction to
a particular invalid relative-extension quantifier order.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- For ANY actual old reserved stage with two genuine selected
source leaves, and ANY original unordered induced generic
target true-leaf range F, one can choose a whole induced generic
true-leaf subcopy U inside F beyond M which has NO compatible
reserved immediate successor image for that FIXED old stage.

The source/target old vertex images are fixed; only the target
generic leaf copy is refined. No assumption that the original
F is ordered is made. -/
theorem RoleDiary.exists_generic_subcopy_avoiding_all_fixed_old_stage_successors
    {H K : Ordered3Graph Nat} (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ n : Nat, IsLeaf K (F n))
    {m a b : Nat} (f : Nat → Nat)
    (P : ReservedDiaryStage H K F m f)
    (hm : IsLeaf H m)
    (ha : a ∈ countableDiaryLeafPrefix H m)
    (hb : b ∈ countableDiaryLeafPrefix H m)
    (hab : a < b)
    (M : Nat) :
    ∃ U : Ordered3Graph.UnorderedEmbedding G.graph K,
      ∀ n : Nat,
        M < U n ∧ IsLeaf K (U n) ∧
        (∃ t : Nat, U n = F t) ∧
        ¬ HasCompatibleReservedNextLeaf H K F f m (U n) := by
  classical
  obtain ⟨J,hRange,c,hCopies,hBad⟩ :=
    DK.exists_bad_cofinal_generic_monochromatic_subcopies_for_old_stage
      G F hFLeaf f P hm ha hb hab
  obtain ⟨u,hu,hAll⟩ := hCopies M
  let U : Ordered3Graph.UnorderedEmbedding G.graph K := {
    toFun := fun n => J (u n)
    injective := J.injective.comp u.strictMono.injective
    edge_iff := by
      intro x y z hxy hyz
      calc
        G.graph.unorderedEdge x y z ↔ G.graph.edge x y z :=
          G.graph.unorderedEdge_iff_of_lt x y z hxy hyz
        _ ↔ G.graph.edge (u x) (u y) (u z) :=
          u.edge_iff hxy hyz
        _ ↔ G.graph.unorderedEdge (u x) (u y) (u z) :=
          (G.graph.unorderedEdge_iff_of_lt
            (u x) (u y) (u z)
            (u.strictMono hxy) (u.strictMono hyz)).symm
        _ ↔ K.unorderedEdge (J (u x)) (J (u y)) (J (u z)) :=
          J.edge_iff (u x) (u y) (u z)
            (u.strictMono hxy) (u.strictMono hyz)
  }
  refine ⟨U, ?_⟩
  intro n
  obtain ⟨hM, hColour⟩ := hAll n
  obtain ⟨_hB, hLeaf, t, hF⟩ := hRange (u n)
  have hForbidden :
      ¬ HasCompatibleReservedNextLeaf H K F f m (U n) := by
    intro hGood
    exact (hBad (U n) hGood) hColour
  exact ⟨hM, hLeaf, ⟨t, hF⟩, hForbidden⟩

/-- The actual finite candidate API makes the no-go obstruction
algorithmically precise: for a full source RoleDiary H,
every leaf of the same induced generic refined target copy
fails the COMPLETE new-leaf generator-table criterion WITH
future order reserve for the original fixed old stage.

The failure may concern S1/S2 numeric meets, E2/E3/E5
incidences, order, roles or future reserve; the theorem
does not insist on a single common failed field. -/
theorem RoleDiary.exists_generic_subcopy_avoiding_full_reserved_finite_candidates
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ n : Nat, IsLeaf K (F n))
    {m a b : Nat} (f : Nat → Nat)
    (P : ReservedDiaryStage H K F m f)
    (hm : IsLeaf H m)
    (ha : a ∈ countableDiaryLeafPrefix H m)
    (hb : b ∈ countableDiaryLeafPrefix H m)
    (hab : a < b)
    (M : Nat) :
    ∃ U : Ordered3Graph.UnorderedEmbedding G.graph K,
      ∀ n : Nat,
        M < U n ∧ IsLeaf K (U n) ∧
        (∃ t : Nat, U n = F t) ∧
        ¬ (FiniteNewLeafCandidateCondition H K F m f (U n) ∧
          FutureOrderReserve H (m + 1)
            (candidateNewLeafTableMap H K m f (U n))) := by
  obtain ⟨U,hAll⟩ :=
    DK.exists_generic_subcopy_avoiding_all_fixed_old_stage_successors
      G F hFLeaf f P hm ha hb hab M
  refine ⟨U, ?_⟩
  intro n
  obtain ⟨hM,hLeaf,hF,hForbidden⟩ := hAll n
  refine ⟨hM,hLeaf,hF,?_⟩
  intro hCandidate
  exact hForbidden
    ((P.finite_candidate_iff_compatible_next_leaf DH hm).mp
      hCandidate)

end DiaryLeafPriority
end ThreeUniformDiaries
