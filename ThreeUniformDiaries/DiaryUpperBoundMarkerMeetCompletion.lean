import ThreeUniformDiaries.DiaryUpperBoundReservedCandidateLift
import ThreeUniformDiaries.DiaryCountableInducedPreembeddingFullMeets

/-!
# Track A: complete marker-containing numerical meets and type-respect

The countable coherent diary fusion theorem proves ALL numerical one-
and two-type meets of NONMARKER source vertices and marker fixation
0/1/2. The manuscript's diary-embedding definition, however, tests
arbitrary singleton types and ordered-pair types, including pairs whose
first vertex is a marker. Treating the previous result as a complete
type-respecting embedding without checking those cases is a gap.

For any increasing INDUCED embedding fixing the first three indices,
all type comparisons below a cut <= 3 are literally reflected, since
there are no omitted target marker indices. Consequently a capped
singleton or pair-type meet with a first coordinate below 3 is
preserved exactly. Combining this with the verified nonmarker meet
theorems proves ALL numerical singleton/full-pair meets.

Finally, every capped numerical meet is the greatest type agreement
cut. Thus preservation of ALL exact meet indices yields full
type-respectingness at arbitrary source cuts, including skipped target
levels. This step is independent of diary axioms and of Ramsey theory.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph
namespace Embedding

variable {H K : Ordered3Graph Nat}

/-- Pointwise identity at all genuine marker cuts from the exact
initial 0,1,2 equations. -/
private theorem fixed_marker_cut (e : Embedding H K)
    (h0 : e 0 = 0) (h1 : e 1 = 1) (h2 : e 2 = 2)
    (x : Nat) (hx : x < 3) : e x = x :=
  DiaryLeafPriority.fixed_three_markers h0 h1 h2 x hx

/-- Every singleton comparison at a cut <=3 is literally
reflected by an induced increasing map fixing the three markers,
provided both compared vertices are above that cut. -/
theorem marker_one_prefix_iff
    (e : Embedding H K)
    (h0 : e 0 = 0) (h1 : e 1 = 1) (h2 : e 2 = 2)
    (l u v : Nat) (hl : l ≤ 3)
    (hlu : l ≤ u) (hlv : l ≤ v) :
    H.SameOneTypeBelow l u v ↔
      K.SameOneTypeBelow l (e u) (e v) := by
  have hFix (x : Nat) (hx : x < 3) : e x = x :=
    e.fixed_marker_cut h0 h1 h2 x hx
  constructor
  · intro hs x y hxy hyl
    have hx3 : x < 3 := by omega
    have hy3 : y < 3 := by omega
    have hyu : y < u := by omega
    have hyv : y < v := by omega
    have hEU : H.edge x y u ↔ K.edge x y (e u) := by
      have h := e.edge_iff hxy hyu
      simpa only [hFix x hx3, hFix y hy3] using h
    have hEV : H.edge x y v ↔ K.edge x y (e v) := by
      have h := e.edge_iff hxy hyv
      simpa only [hFix x hx3, hFix y hy3] using h
    exact hEU.symm.trans ((hs hxy hyl).trans hEV)
  · intro ht x y hxy hyl
    have hx3 : x < 3 := by omega
    have hy3 : y < 3 := by omega
    have hyu : y < u := by omega
    have hyv : y < v := by omega
    have hEU : H.edge x y u ↔ K.edge x y (e u) := by
      have h := e.edge_iff hxy hyu
      simpa only [hFix x hx3, hFix y hy3] using h
    have hEV : H.edge x y v ↔ K.edge x y (e v) := by
      have h := e.edge_iff hxy hyv
      simpa only [hFix x hx3, hFix y hy3] using h
    exact hEU.trans ((ht hxy hyl).trans hEV.symm)

/-- Marker auxiliary pair comparisons are also literally
reflected, including both edges and nonedges at each marker. -/
theorem marker_aux_prefix_iff
    (e : Embedding H K)
    (h0 : e 0 = 0) (h1 : e 1 = 1) (h2 : e 2 = 2)
    (l a b c d : Nat) (hl : l ≤ 3)
    (hla : l ≤ a) (hab : a < b)
    (hlc : l ≤ c) (hcd : c < d) :
    H.SameAuxTypeBelow l a b c d ↔
      K.SameAuxTypeBelow l (e a) (e b) (e c) (e d) := by
  have hFix (x : Nat) (hx : x < 3) : e x = x :=
    e.fixed_marker_cut h0 h1 h2 x hx
  constructor
  · intro hs x hx
    have hx3 : x < 3 := by omega
    have hxa : x < a := by omega
    have hxc : x < c := by omega
    have hEAB : H.edge x a b ↔ K.edge x (e a) (e b) := by
      have h := e.edge_iff hxa hab
      simpa only [hFix x hx3] using h
    have hECD : H.edge x c d ↔ K.edge x (e c) (e d) := by
      have h := e.edge_iff hxc hcd
      simpa only [hFix x hx3] using h
    exact hEAB.symm.trans ((hs hx).trans hECD)
  · intro ht x hx
    have hx3 : x < 3 := by omega
    have hxa : x < a := by omega
    have hxc : x < c := by omega
    have hEAB : H.edge x a b ↔ K.edge x (e a) (e b) := by
      have h := e.edge_iff hxa hab
      simpa only [hFix x hx3] using h
    have hECD : H.edge x c d ↔ K.edge x (e c) (e d) := by
      have h := e.edge_iff hxc hcd
      simpa only [hFix x hx3] using h
    exact hEAB.trans ((ht hx).trans hECD.symm)

/-- Combining singleton coordinates and auxiliary pair bits
gives exact two-type agreement below every initial marker cut. -/
theorem marker_two_prefix_iff
    (e : Embedding H K)
    (h0 : e 0 = 0) (h1 : e 1 = 1) (h2 : e 2 = 2)
    (l a b c d : Nat) (hl : l ≤ 3)
    (hla : l ≤ a) (hab : a < b)
    (hlc : l ≤ c) (hcd : c < d) :
    H.SameTwoTypeBelow l a b c d ↔
      K.SameTwoTypeBelow l (e a) (e b) (e c) (e d) := by
  have hlb : l ≤ b := hla.trans hab.le
  have hld : l ≤ d := hlc.trans hcd.le
  change
    (H.SameOneTypeBelow l a c ∧
     H.SameOneTypeBelow l b d ∧
     H.SameAuxTypeBelow l a b c d) ↔
    (K.SameOneTypeBelow l (e a) (e c) ∧
     K.SameOneTypeBelow l (e b) (e d) ∧
     K.SameAuxTypeBelow l (e a) (e b) (e c) (e d))
  constructor
  · rintro ⟨hs1, hs2, hsAux⟩
    exact ⟨(e.marker_one_prefix_iff h0 h1 h2 l a c hl hla hlc).mp hs1,
      (e.marker_one_prefix_iff h0 h1 h2 l b d hl hlb hld).mp hs2,
      (e.marker_aux_prefix_iff h0 h1 h2 l a b c d
        hl hla hab hlc hcd).mp hsAux⟩
  · rintro ⟨ht1, ht2, htAux⟩
    exact ⟨(e.marker_one_prefix_iff h0 h1 h2 l a c hl hla hlc).mpr ht1,
      (e.marker_one_prefix_iff h0 h1 h2 l b d hl hlb hld).mpr ht2,
      (e.marker_aux_prefix_iff h0 h1 h2 l a b c d
        hl hla hab hlc hcd).mpr htAux⟩

/-- Exact singleton numerical meet at any marker-containing
pair, without any assumptions about target levels beyond 2. -/
theorem oneMeet_preserved_of_marker_min
    (e : Embedding H K)
    (h0 : e 0 = 0) (h1 : e 1 = 1) (h2 : e 2 = 2)
    (u v : Nat) (hSmall : min u v < 3) :
    K.oneMeetLevel (e u) (e v) =
      e (H.oneMeetLevel u v) := by
  classical
  let s := H.oneMeetLevel u v
  let t := K.oneMeetLevel (e u) (e v)
  have hFix (x : Nat) (hx : x < 3) : e x = x :=
    e.fixed_marker_cut h0 h1 h2 x hx
  have hMinMap : min (e u) (e v) = e (min u v) := by
    rcases le_total u v with huv | hvu
    · rw [min_eq_left huv, min_eq_left (e.strictMono.monotone huv)]
    · rw [min_eq_right hvu, min_eq_right (e.strictMono.monotone hvu)]
  have hMin : min (e u) (e v) = min u v :=
    hMinMap.trans (hFix (min u v) hSmall)
  have hsBound : s ≤ min u v := H.oneMeetLevel_le_min u v
  have htBound : t ≤ min u v := by
    have h := K.oneMeetLevel_le_min (e u) (e v)
    simpa only [hMin] using h
  have hSA : H.SameOneTypeBelow s u v := H.oneMeetLevel_agree u v
  have hTA : K.SameOneTypeBelow t (e u) (e v) :=
    K.oneMeetLevel_agree (e u) (e v)
  have hsTarget : K.SameOneTypeBelow s (e u) (e v) :=
    (e.marker_one_prefix_iff h0 h1 h2 s u v
      (by omega) (by omega) (by omega)).mp hSA
  have htSource : H.SameOneTypeBelow t u v :=
    (e.marker_one_prefix_iff h0 h1 h2 t u v
      (by omega) (by omega) (by omega)).mpr hTA
  have hsLeT : s ≤ t := Nat.le_findGreatest (by omega) hsTarget
  have htLeS : t ≤ s := Nat.le_findGreatest (by omega) htSource
  change t = e s
  rw [hFix s (by omega)]
  omega

/-- Exact full ordered-pair meet when one of the first vertices
is a marker. The proof uses all three comparison components,
not merely auxiliary pair incidence. -/
theorem twoMeet_preserved_of_marker_min
    (e : Embedding H K)
    (h0 : e 0 = 0) (h1 : e 1 = 1) (h2 : e 2 = 2)
    (a b c d : Nat) (hab : a < b) (hcd : c < d)
    (hSmall : min a c < 3) :
    K.twoMeetLevel (e a) (e b) (e c) (e d) =
      e (H.twoMeetLevel a b c d) := by
  classical
  let s := H.twoMeetLevel a b c d
  let t := K.twoMeetLevel (e a) (e b) (e c) (e d)
  have hFix (x : Nat) (hx : x < 3) : e x = x :=
    e.fixed_marker_cut h0 h1 h2 x hx
  have hMinMap : min (e a) (e c) = e (min a c) := by
    rcases le_total a c with hac | hca
    · rw [min_eq_left hac, min_eq_left (e.strictMono.monotone hac)]
    · rw [min_eq_right hca, min_eq_right (e.strictMono.monotone hca)]
  have hMin : min (e a) (e c) = min a c :=
    hMinMap.trans (hFix (min a c) hSmall)
  have hsBound : s ≤ min a c := H.twoMeetLevel_le_min a b c d
  have htBound : t ≤ min a c := by
    have h := K.twoMeetLevel_le_min (e a) (e b) (e c) (e d)
    simpa only [hMin] using h
  have hSA : H.SameTwoTypeBelow s a b c d :=
    H.twoMeetLevel_agree a b c d
  have hTA : K.SameTwoTypeBelow t (e a) (e b) (e c) (e d) :=
    K.twoMeetLevel_agree (e a) (e b) (e c) (e d)
  have hsTarget : K.SameTwoTypeBelow s (e a) (e b) (e c) (e d) :=
    (e.marker_two_prefix_iff h0 h1 h2 s a b c d
      (by omega) (by omega) hab (by omega) hcd).mp hSA
  have htSource : H.SameTwoTypeBelow t a b c d :=
    (e.marker_two_prefix_iff h0 h1 h2 t a b c d
      (by omega) (by omega) hab (by omega) hcd).mpr hTA
  have hsLeT : s ≤ t := Nat.le_findGreatest (by omega) hsTarget
  have htLeS : t ≤ s := Nat.le_findGreatest (by omega) htSource
  change t = e s
  rw [hFix s (by omega)]
  omega

/-- Complete numerical meet preservation, including every
marker-containing singleton and ordered pair, from the already
verified nonmarker meet equations and marker fixation. -/
theorem all_exact_meets_of_nonmarker_and_markers
    (e : Embedding H K)
    (h0 : e 0 = 0) (h1 : e 1 = 1) (h2 : e 2 = 2)
    (hOne : ∀ u v : Nat, 3 ≤ u → 3 ≤ v →
      K.oneMeetLevel (e u) (e v) = e (H.oneMeetLevel u v))
    (hTwo : ∀ a b c d : Nat, a < b → c < d →
      3 ≤ a → 3 ≤ c →
      K.twoMeetLevel (e a) (e b) (e c) (e d) =
        e (H.twoMeetLevel a b c d)) :
    (∀ u v : Nat,
      K.oneMeetLevel (e u) (e v) = e (H.oneMeetLevel u v)) ∧
    (∀ a b c d : Nat, a < b → c < d →
      K.twoMeetLevel (e a) (e b) (e c) (e d) =
        e (H.twoMeetLevel a b c d)) := by
  constructor
  · intro u v
    by_cases hSmall : min u v < 3
    · exact e.oneMeet_preserved_of_marker_min h0 h1 h2 u v hSmall
    · exact hOne u v (by omega) (by omega)
  · intro a b c d hab hcd
    by_cases hSmall : min a c < 3
    · exact e.twoMeet_preserved_of_marker_min h0 h1 h2 a b c d
        hab hcd hSmall
    · exact hTwo a b c d hab hcd (by omega) (by omega)

/-- Literal singleton-type agreement at a source cut is exactly
that the cut does not exceed the capped meet. -/
private theorem sameOneTypeBelow_iff_le_meet
    (H : Ordered3Graph Nat) (l u v : Nat)
    (hl : l ≤ min u v) :
    H.SameOneTypeBelow l u v ↔ l ≤ H.oneMeetLevel u v := by
  classical
  constructor
  · intro h
    exact Nat.le_findGreatest hl h
  · intro h x y hxy hyl
    exact H.oneMeetLevel_agree u v hxy (lt_of_lt_of_le hyl h)

/-- The same last-agreement characterisation for the full
two-type, including both singleton coordinates and the pair bit. -/
private theorem sameTwoTypeBelow_iff_le_meet
    (H : Ordered3Graph Nat) (l a b c d : Nat)
    (hl : l ≤ min a c) :
    H.SameTwoTypeBelow l a b c d ↔
      l ≤ H.twoMeetLevel a b c d := by
  classical
  constructor
  · intro h
    exact Nat.le_findGreatest hl h
  · intro h
    obtain ⟨h0, h1, hAux⟩ :=
      H.twoMeetLevel_agree a b c d
    refine ⟨?_, ?_, ?_⟩
    · intro x y hxy hyl
      exact h0 hxy (lt_of_lt_of_le hyl h)
    · intro x y hxy hyl
      exact h1 hxy (lt_of_lt_of_le hyl h)
    · intro x hx
      exact hAux (lt_of_lt_of_le hx h)

/-- A strictly monotone map both preserves and reflects
the order comparisons used in last-agreement cuts. -/
private theorem le_iff_image_le
    (e : Embedding H K) (x y : Nat) :
    x ≤ y ↔ e x ≤ e y := by
  constructor
  · intro h
    exact e.strictMono.monotone h
  · intro h
    by_contra hn
    have hyx : y < x := by omega
    have hlt := e.strictMono hyx
    omega

/-- Exact numerical meet transport implies the entire original
type-respectingness predicate, including selected and skipped
target cuts; no diary axioms are required. -/
theorem typeRespecting_of_all_exact_meets
    (e : Embedding H K)
    (hOne : ∀ u v : Nat,
      K.oneMeetLevel (e u) (e v) = e (H.oneMeetLevel u v))
    (hTwo : ∀ a b c d : Nat, a < b → c < d →
      K.twoMeetLevel (e a) (e b) (e c) (e d) =
        e (H.twoMeetLevel a b c d)) :
    e.TypeRespecting := by
  constructor
  · intro l u v hlu hlv
    have hSource :=
      sameOneTypeBelow_iff_le_meet H l u v (le_min hlu hlv)
    have hTarget :=
      sameOneTypeBelow_iff_le_meet K (e l) (e u) (e v)
        (le_min (e.strictMono.monotone hlu)
          (e.strictMono.monotone hlv))
    have hOrder :
        l ≤ H.oneMeetLevel u v ↔
          e l ≤ K.oneMeetLevel (e u) (e v) := by
      rw [hOne u v]
      exact e.le_iff_image_le l (H.oneMeetLevel u v)
    exact hSource.trans (hOrder.trans hTarget.symm)
  · intro l a b c d hla hab hlc hcd
    have hSource :=
      sameTwoTypeBelow_iff_le_meet H l a b c d (le_min hla hlc)
    have hTarget :=
      sameTwoTypeBelow_iff_le_meet K (e l)
        (e a) (e b) (e c) (e d)
        (le_min (e.strictMono.monotone hla)
          (e.strictMono.monotone hlc))
    have hOrder :
        l ≤ H.twoMeetLevel a b c d ↔
          e l ≤ K.twoMeetLevel (e a) (e b) (e c) (e d) := by
      rw [hTwo a b c d hab hcd]
      exact e.le_iff_image_le l (H.twoMeetLevel a b c d)
    exact hSource.trans (hOrder.trans hTarget.symm)

/-- Every marker-fixing, fully induced embedding with all
nonmarker numeric meet equations is ACTUALLY type-respecting
on arbitrary singleton and full pair types, as the manuscript
requires of a diary-embedding. -/
theorem typeRespecting_of_nonmarker_exact_meets_and_markers
    (e : Embedding H K)
    (h0 : e 0 = 0) (h1 : e 1 = 1) (h2 : e 2 = 2)
    (hOne : ∀ u v : Nat, 3 ≤ u → 3 ≤ v →
      K.oneMeetLevel (e u) (e v) = e (H.oneMeetLevel u v))
    (hTwo : ∀ a b c d : Nat, a < b → c < d →
      3 ≤ a → 3 ≤ c →
      K.twoMeetLevel (e a) (e b) (e c) (e d) =
        e (H.twoMeetLevel a b c d)) :
    e.TypeRespecting := by
  obtain ⟨hOneAll, hTwoAll⟩ :=
    e.all_exact_meets_of_nonmarker_and_markers
      h0 h1 h2 hOne hTwo
  exact e.typeRespecting_of_all_exact_meets hOneAll hTwoAll

end Embedding
end Ordered3Graph
end ThreeUniformDiaries
