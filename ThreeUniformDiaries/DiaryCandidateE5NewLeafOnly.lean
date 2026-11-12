import ThreeUniformDiaries.DiaryFunctionalCandidateOldSupport
import ThreeUniformDiaries.DiaryReducedFiniteCandidateCriterion

/-!
# Track A: E5 for a functional candidate reduces to old-leaf/new-leaf triples

Fix a GENUINE old admissible diary stage and a new true source leaf m.
For any proposed target image v, assume only that the complete S1/S2
new-leaf generator table is functional. It then fixes every image on
the old support, including every old selected leaf.

The exact complete E5 induced edge/nonedge condition on the WHOLE
new finite support is equivalent to testing ONLY triples (a,b,m)
where a<b are already selected old source leaves. All old-leaf
E5 triples are automatically correct by the old genuine stage;
there are no other supported genuine leaves besides the old leaves
and m, by full-diary S1/S2 closure.

This is a useful reduction for the geometric step, where ordinary
genericity of the prescribed outer leaf range realizes the required
old-pair/new-leaf E5 pattern. It does NOT create a functional v, nor
solve mixed E2/E3, exact split placement, future reserve or persistence.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Among all E5 triples in the newly selected finite support S_(m+1),
the only constraints not already inherited from the genuine old stage
are those ending at the new true leaf m.

No source/target candidate role or range assumption is needed beyond
the old admissible map P and functionality of the generator table.
Both edges and nonedges are included in the biconditional. -/
theorem AdmissibleCofinalDiaryStage.functional_candidate_E5_iff_old_leaf_pair_bits
    {H K : Ordered3Graph Nat} {F f : Nat → Nat} {m v : Nat}
    (DH : RoleDiary H)
    (P : AdmissibleCofinalDiaryStage H K F m f)
    (hm : IsLeaf H m)
    (hFunctional : FiniteGeneratorTableFunctional
      (candidateNewLeafGeneratorTable H K m f v)) :
    (∀ a b : Nat,
      a ∈ countableDiaryLeafPrefix H m →
      b ∈ countableDiaryLeafPrefix H m →
      a < b →
      (H.edge a b m ↔ K.edge (f a) (f b) v)) ↔
    (∀ a b c : Nat,
      a ∈ countableDiaryFiniteSupport H (m + 1) →
      b ∈ countableDiaryFiniteSupport H (m + 1) →
      c ∈ countableDiaryFiniteSupport H (m + 1) →
      IsLeaf H a → IsLeaf H b → IsLeaf H c →
      a < b → b < c →
      (H.edge a b c ↔
        K.edge
          (candidateNewLeafTableMap H K m f v a)
          (candidateNewLeafTableMap H K m f v b)
          (candidateNewLeafTableMap H K m f v c))) := by
  classical
  let Lold := countableDiaryLeafPrefix H m
  let L := countableDiaryLeafPrefix H (m + 1)
  let q := candidateNewLeafTableMap H K m f v
  have hOld : ∀ x : Nat,
      x ∈ countableDiaryFiniteSupport H m → q x = f x :=
    P.functional_candidate_table_preserves_old_support hFunctional
  have hmSelected : m ∈ L :=
    (mem_countableDiaryLeafPrefix_iff H (m + 1) m).mpr
      ⟨hm.1, by omega, hm⟩
  have hNew : q m = v := by
    change finiteGeneratorTableValue
      (candidateNewLeafGeneratorTable H K m f v) m = v
    have hRow :
        (m,candidateLeafImage f m v m) ∈
          candidateNewLeafGeneratorTable H K m f v :=
      finiteLeafGeneratorTable_leaf H K L
        (candidateLeafImage f m v) m hmSelected
    have hValue :=
      finiteGeneratorTableValue_eq_of_mem
        (candidateNewLeafGeneratorTable H K m f v)
        hFunctional m (candidateLeafImage f m v m) hRow
    simpa only [candidateLeafImage, if_pos rfl] using hValue
  have hLLeaf (x : Nat) (hx : x ∈ L) : IsLeaf H x :=
    ((mem_countableDiaryLeafPrefix_iff H (m + 1) x).mp hx).2.2
  have hSelected (x : Nat)
      (hx : x ∈ countableDiaryFiniteSupport H (m + 1))
      (hLeaf : IsLeaf H x) : x ∈ L :=
    finiteLeafMeetSupport_leaf_mem_L DH hLLeaf hx hLeaf
  have hOldLeaf (x : Nat) (hx : x ∈ L)
      (hxm : x < m) : x ∈ Lold := by
    obtain ⟨hx3,_,hxLeaf⟩ :=
      (mem_countableDiaryLeafPrefix_iff H (m + 1) x).mp hx
    exact (mem_countableDiaryLeafPrefix_iff H m x).mpr
      ⟨hx3,hxm,hxLeaf⟩
  have hOldSupported (x : Nat) (hx : x ∈ Lold) :
      x ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_leaf H Lold x hx
  constructor
  · intro hNewBits a b c haS hbS hcS ha hb hc hab hbc
    have haL : a ∈ L := hSelected a haS ha
    have hbL : b ∈ L := hSelected b hbS hb
    have hcL : c ∈ L := hSelected c hcS hc
    have hcBefore : c < m + 1 :=
      ((mem_countableDiaryLeafPrefix_iff H (m + 1) c).mp hcL).2.1
    by_cases hcm : c = m
    · subst c
      have haOld : a ∈ Lold :=
        hOldLeaf a haL (by omega)
      have hbOld : b ∈ Lold :=
        hOldLeaf b hbL (by omega)
      change H.edge a b m ↔ K.edge (q a) (q b) (q m)
      rw [hOld a (hOldSupported a haOld),
        hOld b (hOldSupported b hbOld), hNew]
      exact hNewBits a b haOld hbOld hab
    · have hclt : c < m := by omega
      have halt : a < m := by omega
      have hblt : b < m := by omega
      have haOld : a ∈ Lold := hOldLeaf a haL halt
      have hbOld : b ∈ Lold := hOldLeaf b hbL hblt
      have hcOld : c ∈ Lold := hOldLeaf c hcL hclt
      change H.edge a b c ↔ K.edge (q a) (q b) (q c)
      rw [hOld a (hOldSupported a haOld),
        hOld b (hOldSupported b hbOld),
        hOld c (hOldSupported c hcOld)]
      exact P.induced_edge a b c
        (hOldSupported a haOld)
        (hOldSupported b hbOld)
        (hOldSupported c hcOld) hab hbc
  · intro hFull a b haOld hbOld hab
    have hbLt : b < m :=
      ((mem_countableDiaryLeafPrefix_iff H m b).mp hbOld).2.1
    have haLeaf : IsLeaf H a :=
      ((mem_countableDiaryLeafPrefix_iff H m a).mp haOld).2.2
    have hbLeaf : IsLeaf H b :=
      ((mem_countableDiaryLeafPrefix_iff H m b).mp hbOld).2.2
    have haS : a ∈ countableDiaryFiniteSupport H (m + 1) :=
      mem_finiteLeafMeetSupport_leaf H L a
        ((countableDiaryLeafPrefix_mono H m (m + 1) (by omega)) haOld)
    have hbS : b ∈ countableDiaryFiniteSupport H (m + 1) :=
      mem_finiteLeafMeetSupport_leaf H L b
        ((countableDiaryLeafPrefix_mono H m (m + 1) (by omega)) hbOld)
    have hmS : m ∈ countableDiaryFiniteSupport H (m + 1) :=
      mem_finiteLeafMeetSupport_leaf H L m hmSelected
    have hIncidence := hFull a b m haS hbS hmS
      haLeaf hbLeaf hm hab hbLt
    change H.edge a b m ↔ K.edge (q a) (q b) (q m)
      at hIncidence
    rw [hOld a (hOldSupported a haOld),
      hOld b (hOldSupported b hbOld), hNew] at hIncidence
    exact hIncidence

end DiaryLeafPriority
end ThreeUniformDiaries
