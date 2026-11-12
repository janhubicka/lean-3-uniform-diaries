import ThreeUniformDiaries.DiaryCofinalBadGenericNextLeafColour
import ThreeUniformDiaries.DiaryGenericE5FullColourS1S2Reservoir

/-!
# Track A: entirely BAD complete colours can contain induced GENERIC subcopies

For an actual old reserved diary stage with two selected old leaves,
the preceding theorem supplies a bad complete old-cut singleton colour
which is cofinally populated by genuine target leaves: it has the
opposite E5 bit over the fixed old target leaf pair, so it admits
no compatible relative reserved next-leaf successor.

Here we upgrade the positive reservoir from individual leaves
to an ENTIRE induced generic true-leaf subcopy in the original
unordered generic target range. The checked Track C theorem first
builds an actual induced generic leaf copy entirely inside a chosen
finite old-E5 pattern fibre, including the WRONG prescribed
old-pair bit. It then refines to induced generic subcopies with
one COMPLETE singleton colour beyond EVERY numerical bound.

Thus even a truly cofinal homogeneous generic subcopy can be
wholly source-incompatible. This does not rule out a different
good colour or a more careful source-compatible fusion, and it
does not establish countable diary unavoidability or its negation.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

private theorem unorderedEdge_swap_first
    (K : Ordered3Graph Nat) (x y z : Nat) :
    K.unorderedEdge x y z ↔ K.unorderedEdge y x z := by
  unfold Ordered3Graph.unorderedEdge
  constructor
  · intro h
    rcases h with h | h | h | h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · intro h
    rcases h with h | h | h | h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

/-- In the original arbitrary UNORDERED induced generic true-leaf
range of a full target RoleDiary K, for any genuine old reserved
stage with two selected source leaves a<b there is one induced
generic true-leaf subcopy J[G] and ONE full old-cut colour c
such that generic monochromatic subcopies of J[G] occur beyond
EVERY target bound, yet NO genuine compatible reserved immediate
successor of the fixed old stage has colour c.

The target J is an ACTUAL unordered induced generic copy, not
just an infinite set, and all its vertices are in the original
F range. A source-required wrong E5 bit makes the selected full
colour wholly bad. -/
theorem RoleDiary.exists_bad_cofinal_generic_monochromatic_subcopies_for_old_stage
    {H K : Ordered3Graph Nat} (DK : RoleDiary K)
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ n : Nat, IsLeaf K (F n))
    {m a b : Nat} (f : Nat → Nat)
    (P : ReservedDiaryStage H K F m f)
    (hm : IsLeaf H m)
    (ha : a ∈ countableDiaryLeafPrefix H m)
    (hb : b ∈ countableDiaryLeafPrefix H m)
    (hab : a < b) :
    let B := oldStageTailCut H m f
    ∃ J : Ordered3Graph.UnorderedEmbedding G.graph K,
      (∀ n : Nat, B < J n ∧ IsLeaf K (J n) ∧
        ∃ t : Nat, J n = F t) ∧
      ∃ c : Fin B → Fin B → Bool,
        (∀ M : Nat,
          ∃ (u : Ordered3Graph.Embedding G.graph G.graph),
            u.AuxTypeRespecting ∧
            ∀ n : Nat, M < J (u n) ∧
              DiaryLowerBoundColors.singletonColour K B (J (u n)) = c) ∧
        (∀ w : Nat, HasCompatibleReservedNextLeaf H K F f m w →
          DiaryLowerBoundColors.singletonColour K B w ≠ c) := by
  classical
  let B := oldStageTailCut H m f
  have haOld : a ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H m) a ha
  have hbOld : b ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H m) b hb
  have hOrder : f a < f b := P.1.ordered a b haOld hbOld hab
  obtain ⟨i, hi⟩ := P.1.leaf_range a haOld
    ((mem_countableDiaryLeafPrefix_iff H m a).mp ha).2.2
  obtain ⟨j, hj⟩ := P.1.leaf_range b hbOld
    ((mem_countableDiaryLeafPrefix_iff H m b).mp hb).2.2
  have hIJ : i ≠ j := by
    intro heq
    have hSame : f a = f b := by
      calc
        f a = F i := hi
        _ = F j := congrArg F heq
        _ = f b := hj.symm
    exact (ne_of_lt hOrder) hSame
  have hOldB : f b < B := by
    change f b <
      max ((countableDiaryFiniteSupport H m).sup f)
        ((countableDiaryLeafPrefix H m).sup f) + 1
    calc
      f b ≤ (countableDiaryLeafPrefix H m).sup f :=
        Finset.le_sup (f := f) hb
      _ ≤ max ((countableDiaryFiniteSupport H m).sup f)
          ((countableDiaryLeafPrefix H m).sup f) :=
        le_max_right _ _
      _ < max ((countableDiaryFiniteSupport H m).sup f)
          ((countableDiaryLeafPrefix H m).sup f) + 1 :=
        Nat.lt_succ_self _
  let A : Finset Nat := {i, j}
  let theta : Nat → Nat → Bool :=
    fun _ _ => oppositeOldPairE5Bit H a b m
  have hiA : i ∈ A := by simp [A]
  have hjA : j ∈ A := by simp [A]
  have hRoots : ∀ w : Nat, w ∈ (∅ : Finset Nat) → IsLeaf K w := by
    intro w hw
    simp at hw
  obtain ⟨J, hRange, hAbove, hPattern,
      c, _p, _q, _hOne, _hTwo, hCopies⟩ :=
    DK.exists_uniform_generic_oldE5_fullColour_S1_S2_reservoir
      G F hFLeaf A theta ∅ hRoots B B
  have hUnorderedWrong (n : Nat) :
      K.unorderedEdge (F i) (F j) (J n) ↔
        ¬ H.edge a b m := by
    rcases lt_trichotomy i j with hij | heq | hji
    · have h := hPattern n i j hiA hjA hij
      simpa [theta, oppositeOldPairE5Bit] using h
    · exact False.elim (hIJ heq)
    · have h := hPattern n j i hjA hiA hji
      calc
        K.unorderedEdge (F i) (F j) (J n) ↔
            K.unorderedEdge (F j) (F i) (J n) :=
          unorderedEdge_swap_first K (F i) (F j) (J n)
        _ ↔ ¬ H.edge a b m := by
          simpa [theta, oppositeOldPairE5Bit] using h
  have hWrongAt (n : Nat) :
      ¬ (H.edge a b m ↔ K.edge (f a) (f b) (J n)) := by
    have hLate : f b < J n := by
      have hFj := hAbove n j hjA
      simpa only [← hj] using hFj
    have hUnordered :
        K.unorderedEdge (f a) (f b) (J n) ↔
          ¬ H.edge a b m := by
      simpa only [hi, hj] using hUnorderedWrong n
    have hOpp :
        K.edge (f a) (f b) (J n) ↔
          ¬ H.edge a b m :=
      (K.unorderedEdge_iff_of_lt
        (f a) (f b) (J n) hOrder hLate).symm.trans hUnordered
    intro hGood
    have hContr : H.edge a b m ↔ ¬ H.edge a b m :=
      hGood.trans hOpp
    tauto
  have hNoGood (w : Nat)
      (hGood : HasCompatibleReservedNextLeaf H K F f m w) :
      DiaryLowerBoundColors.singletonColour K B w ≠ c := by
    obtain ⟨u, _hu, hAll⟩ := hCopies 0
    have hAnchorColour :
        DiaryLowerBoundColors.singletonColour K B (J (u 0)) = c :=
      (hAll 0).2.2.1
    have hBad :=
      P.wrong_old_pair_E5_bit_forbids_compatible_colour
        hm ha hb hab hOldB (hWrongAt (u 0)) w hGood
    intro hSame
    exact hBad (hSame.trans hAnchorColour.symm)
  refine ⟨J, hRange, c, ?_, hNoGood⟩
  intro M
  obtain ⟨u, hu, hAll⟩ := hCopies M
  refine ⟨u, hu, ?_⟩
  intro n
  exact ⟨(hAll n).1, (hAll n).2.2.1⟩

end DiaryLeafPriority
end ThreeUniformDiaries
