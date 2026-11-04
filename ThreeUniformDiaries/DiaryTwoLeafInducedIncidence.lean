import ThreeUniformDiaries.DiaryTwoLeafFiveEdgeShapes
import ThreeUniformDiaries.DiaryTwoLeafMarkerOrientation

/-!
# The one-bit theorem controls the full two-leaf induced edge table

For the six-coordinate support of any two genuine selected leaves,
a strictly increasing support map that fixes the three markers,
carries the old/new leaves to two genuine target leaves, and carries
their singleton meet to the exact target singleton meet preserves
and reflects EVERY increasing hyperedge (including all nonedges)
if the single right split/leaf bit agrees.

The proof uses the five-shape classification, not an assumption that
genericity of the unordered leaf reduct controls mixed incidences.
This is an induced-table lemma, not existence of a suitable new leaf.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A single right marker bit is sufficient to preserve the entire
induced edge/nonedge table on the genuine two-leaf support, once its
six-coordinate order and singleton meet are mapped correctly. -/
theorem twoLeaf_induced_edge_iff_right_bit
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (a b c d : Nat)
    (ha : IsLeaf H a) (hb : IsLeaf H b) (hab : a < b)
    (hc : IsLeaf K c) (hd : IsLeaf K d) (hcd : c < d)
    (f : Nat → Nat)
    (hMark : ∀ i : Nat, i < 3 → f i = i)
    (hMeet : f (H.oneMeetLevel a b) = K.oneMeetLevel c d)
    (hA : f a = c) (hB : f b = d)
    (hOrder : ∀ u v : Nat,
      u ∈ finiteLeafMeetSupport H ({a,b} : Finset Nat) →
      v ∈ finiteLeafMeetSupport H ({a,b} : Finset Nat) →
      u < v → f u < f v)
    (hBit :
      (H.edge 0 (H.oneMeetLevel a b) b ↔
        K.edge 0 (K.oneMeetLevel c d) d)) :
    ∀ x y z : Nat,
      x ∈ finiteLeafMeetSupport H ({a,b} : Finset Nat) →
      y ∈ finiteLeafMeetSupport H ({a,b} : Finset Nat) →
      z ∈ finiteLeafMeetSupport H ({a,b} : Finset Nat) →
      x < y → y < z →
      (H.edge x y z ↔ K.edge (f x) (f y) (f z)) := by
  classical
  let s := H.oneMeetLevel a b
  let t := K.oneMeetLevel c d
  let S := finiteLeafMeetSupport H ({a,b} : Finset Nat)
  let T := finiteLeafMeetSupport K ({c,d} : Finset Nat)
  have hsOne : IsOneSplit H s :=
    DH.singleton_meets a b ha hb (ne_of_lt hab)
  have htOne : IsOneSplit K t :=
    DK.singleton_meets c d hc hd (ne_of_lt hcd)
  have h0Image : f 0 = 0 := hMark 0 (by omega)
  have h1Image : f 1 = 1 := hMark 1 (by omega)
  have h2Image : f 2 = 2 := hMark 2 (by omega)
  have hsImage : f s = t := hMeet
  have h0Mem : 0 ∈ S := mem_finiteLeafMeetSupport_marker H {a,b} 0 (by omega)
  have h1Mem : 1 ∈ S := mem_finiteLeafMeetSupport_marker H {a,b} 1 (by omega)
  have h2Mem : 2 ∈ S := mem_finiteLeafMeetSupport_marker H {a,b} 2 (by omega)
  have hsMem : s ∈ S :=
    mem_finiteLeafMeetSupport_oneMeet H {a,b} a b
      (by simp) (by simp) (ne_of_lt hab)
  have haMem : a ∈ S :=
    mem_finiteLeafMeetSupport_leaf H {a,b} a (by simp)
  have hbMem : b ∈ S :=
    mem_finiteLeafMeetSupport_leaf H {a,b} b (by simp)
  have hSourceCases : ∀ u : Nat, u ∈ S →
      u < 3 ∨ u = a ∨ u = b ∨ u = s := by
    intro u hu
    change u ∈ finiteLeafMeetSupport H ({a,b} : Finset Nat) at hu
    rw [DH.twoLeafSupport_eq a b ha hb hab] at hu
    simpa only [Finset.mem_union, Finset.mem_range,
      Finset.mem_insert, Finset.mem_singleton] using hu
  have hMap : ∀ u : Nat, u ∈ S → f u ∈ T := by
    intro u hu
    rcases hSourceCases u hu with hSmall | hEq | hEq | hEq
    · rw [hMark u hSmall]
      exact mem_finiteLeafMeetSupport_marker K {c,d} u hSmall
    · subst u
      rw [hA]
      exact mem_finiteLeafMeetSupport_leaf K {c,d} c (by simp)
    · subst u
      rw [hB]
      exact mem_finiteLeafMeetSupport_leaf K {c,d} d (by simp)
    · subst u
      rw [hsImage]
      exact mem_finiteLeafMeetSupport_oneMeet K {c,d} c d
        (by simp) (by simp) (ne_of_lt hcd)
  have hInject : ∀ u v : Nat, u ∈ S → v ∈ S →
      f u = f v → u = v := by
    intro u v hu hv heq
    rcases lt_trichotomy u v with hlt | heqUV | hgt
    · have hlt' := hOrder u v hu hv hlt
      omega
    · exact heqUV
    · have hgt' := hOrder v u hv hu hgt
      omega
  obtain ⟨hLeft,hM1,hM2⟩ :=
    two_leaf_right_orientation_controls_marker_profile
      DH DK a b c d hab hcd ha hb hc hd hBit
  intro x y z hx hy hz hxy hyz
  constructor
  · intro he
    obtain hShape :=
      DH.twoLeafSupportedEdge_shapes a b ha hb hab x y z hx hy hz he
    dsimp at hShape
    rcases hShape with ⟨hx0,hy1,hzS⟩ |
      ⟨hx0,hyS,hzAB⟩ | ⟨hx12,hyA,hzB⟩
    · subst x
      subst y
      subst z
      simpa only [h0Image,h1Image,hsImage] using htOne.2.1
    · subst x
      subst y
      rcases hzAB with hzA | hzB
      · subst z
        have hK : K.edge 0 t c := hLeft.mp he
        simpa only [h0Image,hsImage,hA] using hK
      · subst z
        have hK : K.edge 0 t d := hBit.mp he
        simpa only [h0Image,hsImage,hB] using hK
    · subst y
      subst z
      rcases hx12 with hx1 | hx2
      · subst x
        have hK : K.edge 1 c d := hM1.mp he
        simpa only [h1Image,hA,hB] using hK
      · subst x
        have hK : K.edge 2 c d := hM2.mp he
        simpa only [h2Image,hA,hB] using hK
  · intro he
    obtain hShape :=
      DK.twoLeafSupportedEdge_shapes c d hc hd hcd
        (f x) (f y) (f z) (hMap x hx) (hMap y hy) (hMap z hz) he
    dsimp at hShape
    rcases hShape with ⟨hX0,hY1,hZT⟩ |
      ⟨hX0,hYT,hZCD⟩ | ⟨hX12,hYC,hZD⟩
    · have hx0 : x = 0 :=
        hInject x 0 hx h0Mem (hX0.trans h0Image.symm)
      have hy1 : y = 1 :=
        hInject y 1 hy h1Mem (hY1.trans h1Image.symm)
      have hzS : z = s :=
        hInject z s hz hsMem (hZT.trans hsImage.symm)
      subst x
      subst y
      subst z
      exact hsOne.2.1
    · have hx0 : x = 0 :=
        hInject x 0 hx h0Mem (hX0.trans h0Image.symm)
      have hyS : y = s :=
        hInject y s hy hsMem (hYT.trans hsImage.symm)
      subst x
      subst y
      rcases hZCD with hZC | hZD
      · have hzA : z = a :=
          hInject z a hz haMem (hZC.trans hA.symm)
        subst z
        have hK : K.edge 0 t c := by
          simpa only [h0Image,hsImage,hA] using he
        exact hLeft.mpr hK
      · have hzB : z = b :=
          hInject z b hz hbMem (hZD.trans hB.symm)
        subst z
        have hK : K.edge 0 t d := by
          simpa only [h0Image,hsImage,hB] using he
        exact hBit.mpr hK
    · have hyA : y = a :=
        hInject y a hy haMem (hYC.trans hA.symm)
      have hzB : z = b :=
        hInject z b hz hbMem (hZD.trans hB.symm)
      subst y
      subst z
      rcases hX12 with hX1 | hX2
      · have hx1 : x = 1 :=
          hInject x 1 hx h1Mem (hX1.trans h1Image.symm)
        subst x
        have hK : K.edge 1 c d := by
          simpa only [h1Image,hA,hB] using he
        exact hM1.mpr hK
      · have hx2 : x = 2 :=
          hInject x 2 hx h2Mem (hX2.trans h2Image.symm)
        subst x
        have hK : K.edge 2 c d := by
          simpa only [h2Image,hA,hB] using he
        exact hM2.mpr hK

end DiaryLeafPriority
end ThreeUniformDiaries
