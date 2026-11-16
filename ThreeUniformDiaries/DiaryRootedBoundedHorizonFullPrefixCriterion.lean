import ThreeUniformDiaries.DiaryPersistentStableCompleteInitialPrefix
import ThreeUniformDiaries.DiaryRootedSplitBoundedPersistence

/-!
# Track A: bounded ROOTED next-leaf horizons iff coherent full prefix through the leaf

The already verified exact rooted-split finite-choice theorem
selects one ACTUAL finitely persistent next source-leaf stage g
from a uniform numerical bound B on its image through cofinally
late REAL future reserved source horizons, with one fixed target
rooted S1 meet s and literal agreement on all original old S_m.

The newly checked full OLD-BOUNDED prefix theorem applies to g
at stage m+1, because the next genuine leaf m is NOW a supported
source vertex. This upgrades a single persistent g(m) to one
COMPLETE image table h for EVERY source position u<=m:
strict order, target roles, original true-leaf range,
induced ternary edges AND nonedges, exact numerical singleton
S1 and complete ordered-pair S2 meets. The SAME h recurs
through ALL future genuinely reserved finite stages.

The converse is immediate: a fixed new prefix h gives a
numerical bound B=h(m) at cofinally many source horizons.
Therefore cofinal BOUNDED rooted continuations are equivalent
to the full old-compatible horizon-stable prefix through m.

No such bounded source-relative continuations are established
from generic leaf-range existence, high favourable splits,
cofinal immediate successor cones, or the finite absorber.
This is a correct strictly CONDITIONAL interface, not full
countable diary unavoidability, Ramsey, or exact strong upper.

English-first proof:
notes/track_a_rooted_bounded_horizon_iff_full_prefix_20261116.md
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A uniform numerical bound for ACTUAL compatible new-leaf
images lying at ONE prescribed target rooted singleton split s,
through ARBITRARILY late finite SOURCE horizons, is EQUIVALENT
to one real complete initial source prefix h on ALL [0,m] with:
  - the same rooted target meet s;
  - full bounded, strict, role and prescribed-range preservation;
  - all induced edges AND nonedges;
  - the exact numerical S1 and S2 diary leaf meets;
  - genuine old-f-compatible future reserved realizations at
    EVERY later source horizon, literally fixing ALL h(u), u<=m.

The bound/h map is chosen BEFORE the universal source-horizon
quantifier. No target genericity or RoleDiary K is assumed.
The source H is a real full RoleDiary; the next source leaf m
is genuine. The theorem does NOT prove either side unconditionally. -/
theorem RoleDiary.cofinal_bounded_rooted_nextLeaf_iff_stable_complete_newLeaf_prefix
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H)
    {F f : Nat → Nat} {m w s : Nat}
    (hm : IsLeaf H m) :
    (∃ B : Nat, ∀ N : Nat,
      ∃ n : Nat, N ≤ n ∧
        ∃ g : Nat → Nat,
          ReservedDiaryStage H K F (m + 1 + n) g ∧
          CofinalDiaryStageCompatible H m f g ∧
          g m ≤ B ∧
          K.oneMeetLevel w (g m) = s) ↔
    (∃ (k : Nat) (h : Nat → Nat),
      K.oneMeetLevel w (h m) = s ∧
      (∀ u : Nat, u ≤ m → h u ≤ h m) ∧
      (∀ u v : Nat, u < v → v ≤ m → h u < h v) ∧
      (∀ u : Nat, u ≤ m → IsLeaf H u → IsLeaf K (h u)) ∧
      (∀ u : Nat, u ≤ m → IsOneSplit H u → IsOneSplit K (h u)) ∧
      (∀ u : Nat, u ≤ m → IsTwoSplit H u → IsTwoSplit K (h u)) ∧
      (∀ u : Nat, u ≤ m → IsLeaf H u →
        ∃ i : Nat, h u = F i) ∧
      (∀ a b c : Nat, a < b → b < c → c ≤ m →
        (H.edge a b c ↔ K.edge (h a) (h b) (h c))) ∧
      (∀ a b : Nat, a ≤ m → b ≤ m →
        IsLeaf H a → IsLeaf H b →
        K.oneMeetLevel (h a) (h b) = h (H.oneMeetLevel a b)) ∧
      (∀ a b c d : Nat, a < b → c < d →
        a ≤ m → b ≤ m → c ≤ m → d ≤ m →
        IsLeaf H a → IsLeaf H b →
        IsLeaf H c → IsLeaf H d →
        K.twoMeetLevel (h a) (h b) (h c) (h d) =
          h (H.twoMeetLevel a b c d)) ∧
      (∀ N : Nat, ∃ g : Nat → Nat,
        ReservedDiaryStage H K F (m + 1 + k + N) g ∧
        CofinalDiaryStageCompatible H m f g ∧
        (∀ u : Nat, u ≤ m → g u = h u))) := by
  classical
  constructor
  · intro hBounded
    obtain ⟨g, Pg, hOld, hRoot⟩ :=
      (persistentReservedNextLeafInRootSplit_iff_cofinallyBoundedRootSplitImages
        (H := H) (K := K) (F := F) (f := f)
        (m := m) (w := w) (s := s) hm).mpr hBounded
    have hmLeafPrefix :
        m ∈ countableDiaryLeafPrefix H (m + 1) :=
      (mem_countableDiaryLeafPrefix_iff H (m + 1) m).mpr
        ⟨hm.1, by omega, hm⟩
    have hmSupported :
        m ∈ countableDiaryFiniteSupport H (m + 1) :=
      mem_finiteLeafMeetSupport_leaf H
        (countableDiaryLeafPrefix H (m + 1)) m hmLeafPrefix
    obtain ⟨k, h, hAtM, hBound, hOrder, hLeaf, hOne, hTwo,
        hRange, hEdges, hMeet1, hMeet2, hAll⟩ :=
      Pg.exists_stable_complete_initial_prefix_below_supported_vertex
        DH hmSupported
    have hRootH : K.oneMeetLevel w (h m) = s := by
      rw [hAtM]
      exact hRoot
    have hBoundH : ∀ u : Nat, u ≤ m → h u ≤ h m := by
      intro u hu
      rw [hAtM]
      exact hBound u hu
    refine ⟨k, h, hRootH, hBoundH, hOrder, hLeaf, hOne, hTwo,
      hRange, hEdges, hMeet1, hMeet2, ?_⟩
    intro N
    obtain ⟨gN, QN, hGCompat, hPrefix⟩ := hAll N
    have hOldCompat : CofinalDiaryStageCompatible H m f gN :=
      CofinalDiaryStageCompatible.trans (Nat.le_succ m)
        hOld hGCompat
    exact ⟨gN, QN, hOldCompat, hPrefix⟩
  · rintro ⟨k, h, hRoot, _hBound, _hOrder, _hLeaf,
        _hOne, _hTwo, _hRange, _hEdges, _hMeet1, _hMeet2, hAll⟩
    refine ⟨h m, ?_⟩
    intro N
    obtain ⟨gN, QN, hOld, hPrefix⟩ := hAll N
    have hValue : gN m = h m := hPrefix m (le_refl m)
    have QBounded :
        ReservedDiaryStage H K F (m + 1 + (k + N)) gN := by
      have hEq : m + 1 + (k + N) = m + 1 + k + N := by omega
      simpa only [hEq] using QN
    refine ⟨k + N, by omega, gN, QBounded,
      hOld, le_of_eq hValue, ?_⟩
    rw [hValue]
    exact hRoot

end DiaryLeafPriority
end ThreeUniformDiaries
