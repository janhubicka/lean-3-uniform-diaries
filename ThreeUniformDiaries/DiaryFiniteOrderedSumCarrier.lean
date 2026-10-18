import ThreeUniformDiaries.DiaryPrediaryDefinition
import Mathlib

/-!
# Two finite diary blocks sharing only the three initial markers

A raw finite ordered sum can be built from two finite ordered ternary
edge tables. Each table has marker vertices 0,1,2, and the other
vertices lie in a bounded initial segment. The right nonmarker block
is translated after the left block; only markers are identified.

Cross-block incidence is restricted to Devlin marker triples
(1,u,v) and (2,u,v), with u a left leaf and v a right leaf. One
Boolean orientation per left leaf is a parameter.

This proves the bounded blocks remain INDUCED copies (including
nonedge reflection) and proves increasing edge support. It does
NOT prove global V3 or V1/V2 coherence: those require separately
checking the orientation schedule and split-positive classes.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Edge-only finite frame, a necessary part of being a finite diary.
No finite split witnesses or V/E/S are assumed. -/
structure FiniteDiaryEdgeFrame (H : Ordered3Graph Nat) (n : Nat) : Prop where
  length_ge_three : 3 ≤ n
  edge_support : ∀ a b c : Nat, H.edge a b c →
    a < b ∧ b < c ∧ 3 ≤ c ∧ c < n

/-- Shift the right block after the left, fixing markers 0,1,2. -/
def rightBlockImage (n x : Nat) : Nat :=
  if x < 3 then x else x + (n - 3)

@[simp] theorem rightBlockImage_marker (n x : Nat) (hx : x < 3) :
    rightBlockImage n x = x := by
  simp [rightBlockImage, hx]

theorem rightBlockImage_nonmarker_ge (n x : Nat)
    (hn : 3 ≤ n) (hx : 3 ≤ x) :
    n ≤ rightBlockImage n x := by
  have hnot : ¬ x < 3 := by omega
  simp only [rightBlockImage, if_neg hnot]
  omega

theorem rightBlockImage_strictMono (n : Nat) (hn : 3 ≤ n) :
    StrictMono (rightBlockImage n) := by
  apply strictMono_nat_of_lt_succ
  intro x
  by_cases hx : x < 3
  · by_cases hxs : x + 1 < 3
    · simp only [rightBlockImage, if_pos hx, if_pos hxs]
      omega
    · simp only [rightBlockImage, if_pos hx, if_neg hxs]
      omega
  · have hxs : ¬ x + 1 < 3 := by omega
    simp only [rightBlockImage, if_neg hx, if_neg hxs]
    omega

/-- A raw two-block gluing carrier, with only Devlin marker edges
across blocks. The orientation parameter need not yet satisfy V3. -/
noncomputable def finiteTwoBlockCarrier
    (H K : Ordered3Graph Nat) (n m : Nat)
    (orientation : Nat → Bool) : Ordered3Graph Nat where
  edge x y z :=
    (H.edge x y z ∧ z < n) ∨
    (∃ a b c : Nat, K.edge a b c ∧ c < m ∧
      x = rightBlockImage n a ∧
      y = rightBlockImage n b ∧
      z = rightBlockImage n c) ∨
    (∃ u v : Nat, 3 ≤ u ∧ u < n ∧ IsLeaf H u ∧
      3 ≤ v ∧ v < m ∧ IsLeaf K v ∧
      y = u ∧ z = rightBlockImage n v ∧
      ((x = 1 ∧ orientation u = true) ∨
       (x = 2 ∧ orientation u = false)))

/-- All raw carrier edges have increasing coordinates. -/
theorem finiteTwoBlockCarrier_edge_ordered
    {H K : Ordered3Graph Nat} {n m : Nat}
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (orientation : Nat → Bool) (x y z : Nat)
    (he : (finiteTwoBlockCarrier H K n m orientation).edge x y z) :
    x < y ∧ y < z := by
  rcases he with hLeft | hRight | hCross
  · exact (FH.edge_support x y z hLeft.1).1
  · obtain ⟨a,b,c,hK,_hc,hx,hy,hz⟩ := hRight
    obtain ⟨hab,hbc,_⟩ := FK.edge_support a b c hK
    subst x
    subst y
    subst z
    exact ⟨(rightBlockImage_strictMono n FH.length_ge_three) hab,
      (rightBlockImage_strictMono n FH.length_ge_three) hbc⟩
  · obtain ⟨u,v,hu3,hun,_hLeafU,hv3,_hvm,_hLeafV,hy,hz,hOrientation⟩ := hCross
    have hvRight := rightBlockImage_nonmarker_ge n v FH.length_ge_three hv3
    rcases hOrientation with ⟨hx,_⟩ | ⟨hx,_⟩
    · subst x
      omega
    · subst x
      omega

/-- The finite left block remains induced; later block and cross
edges have third coordinate beyond its last vertex. -/
theorem finiteTwoBlockCarrier_left_edge_iff
    {H K : Ordered3Graph Nat} {n m : Nat}
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (orientation : Nat → Bool)
    (a b c : Nat) (hc : c < n) :
    (finiteTwoBlockCarrier H K n m orientation).edge a b c ↔
      H.edge a b c := by
  constructor
  · intro he
    rcases he with hLeft | hRight | hCross
    · exact hLeft.1
    · obtain ⟨a',b',c',hK,_hcm,_hx,_hy,hz⟩ := hRight
      have hc3 := (FK.edge_support a' b' c' hK).2.2.1
      have hge := rightBlockImage_nonmarker_ge n c' FH.length_ge_three hc3
      omega
    · obtain ⟨u,v,_hu3,_hun,_huLeaf,hv3,_hvm,_hvLeaf,_hy,hz,_hbit⟩ := hCross
      have hge := rightBlockImage_nonmarker_ge n v FH.length_ge_three hv3
      omega
  · intro h
    exact Or.inl ⟨h,hc⟩

/-- The translated right block is induced, including nonedges.
The only overlaps with the left block are the three markers. -/
theorem finiteTwoBlockCarrier_right_edge_iff
    {H K : Ordered3Graph Nat} {n m : Nat}
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (orientation : Nat → Bool)
    (a b c : Nat) (hc : c < m) :
    (finiteTwoBlockCarrier H K n m orientation).edge
      (rightBlockImage n a) (rightBlockImage n b)
      (rightBlockImage n c) ↔ K.edge a b c := by
  constructor
  · intro he
    rcases he with hLeft | hRight | hCross
    · have hc3 := (FH.edge_support _ _ _ hLeft.1).2.2.1
      by_cases hcRight : 3 ≤ c
      · have hge := rightBlockImage_nonmarker_ge n c
          FH.length_ge_three hcRight
        omega
      · have hcSmall : c < 3 := by omega
        rw [rightBlockImage_marker n c hcSmall] at hc3
        omega
    · obtain ⟨a',b',c',hK,_hcm,ha,hb,hc'⟩ := hRight
      have hinj := (rightBlockImage_strictMono n FH.length_ge_three).injective
      have haa : a = a' := hinj ha
      have hbb : b = b' := hinj hb
      have hcc : c = c' := hinj hc'
      rcases haa with rfl
      rcases hbb with rfl
      rcases hcc with rfl
      exact hK
    · obtain ⟨u,v,hu3,hun,_hlu,_hv3,_hvm,_hlv,hy,_hz,_hbit⟩ := hCross
      by_cases hbRight : 3 ≤ b
      · have hge := rightBlockImage_nonmarker_ge n b
          FH.length_ge_three hbRight
        omega
      · have hbSmall : b < 3 := by omega
        rw [rightBlockImage_marker n b hbSmall] at hy
        omega
  · intro hK
    exact Or.inr (Or.inl
      ⟨a,b,c,hK,hc,rfl,rfl,rfl⟩)

/-- The cross Devlin-1 incidence is exactly the chosen orientation
for an actual left leaf and an actual right leaf. -/
theorem finiteTwoBlockCarrier_cross_marker_one
    {H K : Ordered3Graph Nat} {n m : Nat}
    (FH : FiniteDiaryEdgeFrame H n)
    (FK : FiniteDiaryEdgeFrame K m)
    (orientation : Nat → Bool)
    (u v : Nat) (hu3 : 3 ≤ u) (hun : u < n)
    (hlu : IsLeaf H u) (hv3 : 3 ≤ v) (hvm : v < m)
    (hlv : IsLeaf K v) :
    (finiteTwoBlockCarrier H K n m orientation).edge
      1 u (rightBlockImage n v) ↔ orientation u = true := by
  constructor
  · intro he
    rcases he with hLeft | hRight | hCross
    · have hge := rightBlockImage_nonmarker_ge n v
        FH.length_ge_three hv3
      omega
    · obtain ⟨a,b,c,hK,_hc,ha,hb,_hz⟩ := hRight
      have hbImage : rightBlockImage n b = u := hb.symm
      by_cases hb3 : 3 ≤ b
      · have hge := rightBlockImage_nonmarker_ge n b FH.length_ge_three hb3
        omega
      · have hbSmall : b < 3 := by omega
        rw [rightBlockImage_marker n b hbSmall] at hbImage
        omega
    · obtain ⟨u',v',_hu3,_hun,_hlu,_hv3,_hvm,_hlv,hy,hz,hBit⟩ := hCross
      have hu : u' = u := hy.symm
      subst u'
      rcases hBit with hOne | hTwo
      · exact hOne.2
      · omega
  · intro hTrue
    exact Or.inr (Or.inr
      ⟨u,v,hu3,hun,hlu,hv3,hvm,hlv,rfl,rfl,Or.inl ⟨rfl,hTrue⟩⟩)

end DiaryLeafPriority
end ThreeUniformDiaries
