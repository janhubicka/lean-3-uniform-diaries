import ThreeUniformDiaries.DiaryGenericTargetOldE5PatternCopy
import ThreeUniformDiaries.DiaryCofinalBadGenericNextLeafColour

/-!
# Track D: one generic E5-pattern subcopy defeats ALL bounded old supports

Let a<b be TWO genuine earlier selected source diary leaves and m the
next genuine source leaf. Fix any bound B on the target image of b.

The already verified full target-ordered old-E5-pattern theorem creates
ONE genuine induced generic subcopy J of the ORIGINAL arbitrary unordered
generic leaf range F, lying beyond every numerical target threshold,
whose every vertex realizes the OPPOSITE of the prescribed source edge
H.edge a b m over ALL earlier target-ordered F-pairs below B.

For ANY genuine reserved old stage f with f(b)<B, old-stage order and
leaf-range supply indices i,j with f(a)=F(i)<F(j)=f(b)<B.
Consequently every vertex of J has exactly the wrong old-pair E5 bit
for a compatible new-leaf successor over f. This is simultaneous for
ALL such f: the generic J was selected without knowing any f.

This adversarially rules out upgrading Track D via a uniformly bounded
finite list of old supports under the UNORDERED generic-subcopy hitting
hypothesis. The finite-family Ramsey reduction is only conditional,
and its hitting input cannot be obtained by bounding old images here.
No claim is made that the constructed J is an aux-type-respecting
selfcopy, that all possible UNBOUNDED stages are avoided, or that the
full countable diary unavoidability theorem is false.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- At any fixed target bound B and new-leaf cutoff M, for TWO fixed
earlier source leaves a<b, there is one whole induced generic target
leaf subcopy J in the original F-range, ALL of whose vertices are
incompatible with EVERY complete genuine old reserved stage f with
f(b)<B. The same J works for infinitely many possible old maps f;
it is selected solely from the source bit H.edge a b m and B,M.

The obstruction is to bounded-old-support hitting under *unordered*
generic refinements, not to the existential unbounded stages of
#1431/#1435 and not to aux-type-respecting avoidance. -/
theorem exists_generic_leaf_subcopy_avoiding_all_bounded_old_stages
    {H K : Ordered3Graph Nat}
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
      (∀ n : Nat,
        M < J n ∧ B < J n ∧ IsLeaf K (J n) ∧
          ∃ t : Nat, J n = F t) ∧
      (∀ f : Nat → Nat,
        ReservedDiaryStage H K (fun t : Nat => F t) m f →
        f b < B →
        ∀ n : Nat,
          ¬ HasCompatibleReservedNextLeaf H K
            (fun t : Nat => F t) f m (J n)) := by
  classical
  let chi : Nat → Nat → Bool :=
    fun _ _ => decide (¬ H.edge a b m)
  obtain ⟨J, hRange, hPattern⟩ :=
    exists_generic_leaf_subcopy_in_prescribed_target_bounded_E5_pattern
      G K F hFLeaf B M chi
  refine ⟨J, hRange, ?_⟩
  intro f P hBound n hGood
  have haS : a ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H m) a ha
  have hbS : b ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H
      (countableDiaryLeafPrefix H m) b hb
  have hOrder : f a < f b :=
    P.1.ordered a b haS hbS hab
  have haLeaf : IsLeaf H a :=
    ((mem_countableDiaryLeafPrefix_iff H m a).mp ha).2.2
  have hbLeaf : IsLeaf H b :=
    ((mem_countableDiaryLeafPrefix_iff H m b).mp hb).2.2
  obtain ⟨i, hi⟩ := P.1.leaf_range a haS haLeaf
  obtain ⟨j, hj⟩ := P.1.leaf_range b hbS hbLeaf
  have hTargetOrder : F i < F j := by
    simpa only [← hi, ← hj] using hOrder
  have hTargetBound : F j < B := by
    simpa only [← hj] using hBound
  have hOpp :
      (K.edge (f a) (f b) (J n) ↔ ¬ H.edge a b m) := by
    have hMask := hPattern n i j hTargetOrder hTargetBound
    simpa only [← hi, ← hj, chi, decide_eq_true_eq] using hMask
  have hWrong :
      ¬ (H.edge a b m ↔ K.edge (f a) (f b) (J n)) := by
    intro hActual
    have hImpossible : H.edge a b m ↔ ¬ H.edge a b m :=
      hActual.trans hOpp
    tauto
  have hNoColour :=
    P.wrong_old_pair_E5_bit_forbids_compatible_colour
      hm ha hb hab hBound hWrong (J n) hGood
  exact hNoColour rfl

/-- There is NO uniform numerical bound B on the second-old-leaf
image such that every unordered induced generic target-leaf subcopy
contains even one compatible reserved immediate successor over an
old genuine stage satisfying f(b)<B. This is an explicit NEGATION
of the tempting finite/bounded-old-support generic hitting premise.

The generic subcopy is unordered. The theorem does not assert the
corresponding negation for aux-type-respecting source selfcopies. -/
theorem no_uniform_bounded_old_stage_hitting_on_unordered_generic_copies
    {H K : Ordered3Graph Nat}
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    {m a b : Nat}
    (hm : IsLeaf H m)
    (ha : a ∈ countableDiaryLeafPrefix H m)
    (hb : b ∈ countableDiaryLeafPrefix H m)
    (hab : a < b)
    (B : Nat) :
    ¬ (∀ J : Ordered3Graph.UnorderedEmbedding G.graph K,
      (∀ n : Nat, IsLeaf K (J n) ∧
        ∃ t : Nat, J n = F t) →
      ∃ f : Nat → Nat,
        ReservedDiaryStage H K (fun t : Nat => F t) m f ∧
        f b < B ∧
        ∃ n : Nat, HasCompatibleReservedNextLeaf H K
          (fun t : Nat => F t) f m (J n)) := by
  intro hCover
  obtain ⟨J, hRange, hAvoid⟩ :=
    exists_generic_leaf_subcopy_avoiding_all_bounded_old_stages
      G F hFLeaf hm ha hb hab B 0
  obtain ⟨f, P, hBound, n, hGood⟩ :=
    hCover J (fun n => ⟨(hRange n).2.2.1, (hRange n).2.2.2⟩)
  exact hAvoid f P hBound n hGood


/-- A stronger direct corollary: for EVERY finite list of genuine
complete old support stages, one induced unordered generic target leaf
subcopy avoids ALL of the listed compatible next-leaf successors.

No uniform bound is assumed: take B strictly above the finitely
many b-images and apply the stronger all-bounded-stages theorem.
The bound is selected only AFTER receiving the finite list. -/
theorem exists_generic_leaf_subcopy_avoiding_any_finite_old_stage_family
    {H K : Ordered3Graph Nat}
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    {m a b : Nat}
    (hm : IsLeaf H m)
    (ha : a ∈ countableDiaryLeafPrefix H m)
    (hb : b ∈ countableDiaryLeafPrefix H m)
    (hab : a < b)
    (k : Nat) (stages : Fin k → Nat → Nat)
    (hStages : ∀ i : Fin k,
      ReservedDiaryStage H K (fun t : Nat => F t) m (stages i))
    (M : Nat) :
    ∃ J : Ordered3Graph.UnorderedEmbedding G.graph K,
      (∀ n : Nat, M < J n ∧ IsLeaf K (J n) ∧
        ∃ t : Nat, J n = F t) ∧
      (∀ i : Fin k, ∀ n : Nat,
        ¬ HasCompatibleReservedNextLeaf H K
          (fun t : Nat => F t) (stages i) m (J n)) := by
  classical
  let B : Nat :=
    (Finset.univ : Finset (Fin k)).sup (fun i => stages i b) + 1
  obtain ⟨J, hRange, hAvoid⟩ :=
    exists_generic_leaf_subcopy_avoiding_all_bounded_old_stages
      G F hFLeaf hm ha hb hab B M
  refine ⟨J, ?_, ?_⟩
  · intro n
    exact ⟨(hRange n).1, (hRange n).2.2.1, (hRange n).2.2.2⟩
  · intro i n
    have hBound : stages i b < B := by
      have hLe : stages i b ≤
          (Finset.univ : Finset (Fin k)).sup (fun j => stages j b) :=
        Finset.le_sup (f := fun j : Fin k => stages j b)
          (Finset.mem_univ i)
      exact Nat.lt_succ_of_le hLe
    exact hAvoid (stages i) (hStages i) hBound n

/-- No fixed FINITE family of genuine old reserved stages can meet
every UNORDERED induced generic target leaf subcopy by compatible
next-leaf images. This is exact quantifier negation, not a mere
failure of one candidate construction.

It remains compatible with the conditional finite-family theorem
for AUX-TYPE-RESPECTING generic *source selfembeddings*, since the
generic E5-pattern refinement here is only unordered induced. -/
theorem no_finite_old_stages_hit_every_unordered_generic_copy
    {H K : Ordered3Graph Nat}
    (G : GenericEnumerated3Graph)
    (F : Ordered3Graph.UnorderedEmbedding G.graph K)
    (hFLeaf : ∀ t : Nat, IsLeaf K (F t))
    {m a b : Nat}
    (hm : IsLeaf H m)
    (ha : a ∈ countableDiaryLeafPrefix H m)
    (hb : b ∈ countableDiaryLeafPrefix H m)
    (hab : a < b)
    (k : Nat) (stages : Fin k → Nat → Nat)
    (hStages : ∀ i : Fin k,
      ReservedDiaryStage H K (fun t : Nat => F t) m (stages i)) :
    ¬ (∀ J : Ordered3Graph.UnorderedEmbedding G.graph K,
      (∀ n : Nat, IsLeaf K (J n) ∧
        ∃ t : Nat, J n = F t) →
      ∃ i : Fin k, ∃ n : Nat,
        HasCompatibleReservedNextLeaf H K
          (fun t : Nat => F t) (stages i) m (J n)) := by
  intro hHit
  obtain ⟨J, hRange, hAvoid⟩ :=
    exists_generic_leaf_subcopy_avoiding_any_finite_old_stage_family
      G F hFLeaf hm ha hb hab k stages hStages 0
  obtain ⟨i, n, hGood⟩ :=
    hHit J (fun n => (hRange n).2)
  exact hAvoid i n hGood


end DiaryLeafPriority
end ThreeUniformDiaries
