import ThreeUniformDiaries.DiaryFiniteFlipTargetTransport

/-!
# Marker-prefix type transport from a genuinely induced source pullback

The verified pullback of any finite target flip supplies a finite
source flip whose FULL increasing ternary edge/nonedge table is
literally induced from the target along the original vertex map.
That map fixes the distinguished vertices 0,1,2.

Although inducedness alone is insufficient for arbitrary full
singleton/pair-type transport across omitted target vertices,
it is fully sufficient at the initial three marker cuts.
All tests at these cuts use only triples whose first two
coordinates are among 0,1,2.

We formalize the exact two-way transport for singleton and
auxiliary pair prefixes at these early cuts. The results are
purely relational, without any assumed split/leaf E/V/S axioms.
They are the appropriate inputs to the E-only split-meet
dichotomy and the numerical marker transport criterion.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {A T : Ordered3Graph Nat} {n : Nat} {f : Nat → Nat}

/-- The marker-fixing condition extends pointwise to every level
strictly before the first nonmarker cut three. -/
theorem fixed_three_markers
    (h0 : f 0 = 0) (h1 : f 1 = 1) (h2 : f 2 = 2)
    (t : Nat) (ht : t < 3) : f t = t := by
  have h : t = 0 ∨ t = 1 ∨ t = 2 := by omega
  rcases h with h | h | h
  · rw [h]; exact h0
  · rw [h]; exact h1
  · rw [h]; exact h2

/-- Full induced edge/nonedge reflection of the source finite
frame implies exact singleton type agreement at every marker
cut l<=3, for ANY two original nonmarker source vertices.
No target diary axioms or gaps-in-image assumptions are needed. -/
theorem marker_oneType_iff_of_induced
    (h0 : f 0 = 0) (h1 : f 1 = 1) (h2 : f 2 = 2)
    (hInduced : ∀ a b c : Nat, a < b → b < c → c < n →
      (T.edge (f a) (f b) (f c) ↔ A.edge a b c))
    (l u v : Nat) (hl : l ≤ 3)
    (hu3 : 3 ≤ u) (hun : u < n)
    (hv3 : 3 ≤ v) (hvn : v < n) :
    (T.SameOneTypeBelow l (f u) (f v) ↔
      A.SameOneTypeBelow l u v) := by
  constructor
  · intro ht a b hab hb
    have ha3 : a < 3 := by omega
    have hb3 : b < 3 := by omega
    have hFa := fixed_three_markers h0 h1 h2 a ha3
    have hFb := fixed_three_markers h0 h1 h2 b hb3
    have hAU := hInduced a b u hab (by omega) hun
    have hAV := hInduced a b v hab (by omega) hvn
    rw [hFa,hFb] at hAU hAV
    exact hAU.symm.trans ((ht (a := a) (b := b) hab hb).trans hAV)
  · intro hs a b hab hb
    have ha3 : a < 3 := by omega
    have hb3 : b < 3 := by omega
    have hFa := fixed_three_markers h0 h1 h2 a ha3
    have hFb := fixed_three_markers h0 h1 h2 b hb3
    have hAU := hInduced a b u hab (by omega) hun
    have hAV := hInduced a b v hab (by omega) hvn
    rw [hFa,hFb] at hAU hAV
    exact hAU.trans ((hs (a := a) (b := b) hab hb).trans hAV.symm)

/-- Marker auxiliary types of arbitrary ordered nonmarker pairs
are also exactly reflected by the genuinely induced pullback.
The first coordinate of every such test is 0,1,or 2. -/
theorem marker_auxType_iff_of_induced
    (h0 : f 0 = 0) (h1 : f 1 = 1) (h2 : f 2 = 2)
    (hInduced : ∀ a b c : Nat, a < b → b < c → c < n →
      (T.edge (f a) (f b) (f c) ↔ A.edge a b c))
    (l a b c d : Nat) (hl : l ≤ 3)
    (ha3 : 3 ≤ a) (hab : a < b) (hbn : b < n)
    (hc3 : 3 ≤ c) (hcd : c < d) (hdn : d < n) :
    (T.SameAuxTypeBelow l
        (f a) (f b) (f c) (f d) ↔
      A.SameAuxTypeBelow l a b c d) := by
  constructor
  · intro ht x hx
    have hx3 : x < 3 := by omega
    have hFx := fixed_three_markers h0 h1 h2 x hx3
    have hAB := hInduced x a b (by omega) hab hbn
    have hCD := hInduced x c d (by omega) hcd hdn
    rw [hFx] at hAB hCD
    exact hAB.symm.trans ((ht (a := x) hx).trans hCD)
  · intro hs x hx
    have hx3 : x < 3 := by omega
    have hFx := fixed_three_markers h0 h1 h2 x hx3
    have hAB := hInduced x a b (by omega) hab hbn
    have hCD := hInduced x c d (by omega) hcd hdn
    rw [hFx] at hAB hCD
    exact hAB.trans ((hs (a := x) hx).trans hCD.symm)

end DiaryLeafPriority
end ThreeUniformDiaries
