import ThreeUniformDiaries.DiaryFiniteSignRootedPrefixIncidence
import ThreeUniformDiaries.DiaryFiniteUnconditionalFlipOrbitBound

/-!
# Induced raw sign-rooted tree of genuine finite diary flip branches

An actual finite diary A has finitely many genuine source flips.
The verified fixed signature has ONE global Devlin marker-one
coordinate and one source-selected E3 coordinate per genuine
2-split. Instead of the invalid old independent one-split
controls, identify source vertices at level z exactly when
their ROOT SIGN agrees and their E3 coordinates at levels <z
agree. Markers 0,1,2 are shared unconditionally.

This module constructs the relational union of a finite flip
family on these sign-rooted prefix nodes. Branch nodes sharing
a terminal at z have all earlier nodes in common, and their
entire source edge tables ending at z agree by the verified
sign-rooted E1--E5 prefix theorem. Consequently EVERY source
branch is induced, with both edges and nonedges preserved.

This is an actual finite-level RAW relational amalgam, not
a full V/E/S pre-diary. New off-branch Devlin marker edges,
cross-branch V1/V2 coherence, and preservation of protected
mixed meets remain separate geometric obligations. No general
finite absorber is asserted here.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A family of genuine bounded finite flips of the SAME diary. -/
structure FiniteSignRootedFlipFamily
    (A : Ordered3Graph Nat) (n : Nat) (ι : Type*) where
  source : FiniteRoleDiaryBlock A n
  graph : ι → Ordered3Graph Nat
  flip : ∀ i, FiniteDiaryFlip A (graph i) n

/-- The first coordinate records the original source level;
the second is either an empty marker prefix or the global
sign and earlier selected S2 bits. -/
abbrev FiniteSignRootedNode (A : Ordered3Graph Nat) (n : Nat) :=
  Nat × Option (Bool × (FiniteTwoSplitIndex A n → Bool))

namespace FiniteSignRootedFlipFamily

variable {A : Ordered3Graph Nat} {n : Nat} {ι : Type*}

/-- Actual fixed source signature of the i-th genuine flip. -/
noncomputable def signature
    (F : FiniteSignRootedFlipFamily A n ι) (i : ι) :
    Bool × (FiniteTwoSplitIndex A n → Bool) :=
  finiteUnconditionalFlipSignature F.source (F.graph i)

/-- A node at level z shares marker levels 0,1,2 globally;
from level 3 onward it remembers the global sign and only
those source S2 bits at split levels STRICTLY below z. -/
noncomputable def node
    (F : FiniteSignRootedFlipFamily A n ι)
    (i : ι) (z : Nat) : FiniteSignRootedNode A n :=
  (z, if z < 3 then none else
      some ((F.signature i).1,
        fun s => if s.val.val < z then
          (F.signature i).2 s else false))

theorem node_level
    (F : FiniteSignRootedFlipFamily A n ι)
    (i : ι) (z : Nat) : (F.node i z).1 = z := rfl

/-- The three distinguished markers are literally one shared
three-vertex initial segment across the whole family. -/
theorem node_markers_shared
    (F : FiniteSignRootedFlipFamily A n ι)
    (i j : ι) (z : Nat) (hz : z < 3) :
    F.node i z = F.node j z := by
  simp only [node, if_pos hz]

/-- Same node at level z>=3 means same GLOBAL Devlin sign. -/
theorem sign_eq_of_node_eq
    (F : FiniteSignRootedFlipFamily A n ι)
    (i j : ι) (z : Nat)
    (hz : 3 ≤ z)
    (h : F.node i z = F.node j z) :
    (F.signature i).1 = (F.signature j).1 := by
  have hOpt := congrArg
    (fun v : FiniteSignRootedNode A n => v.2) h
  have hNot : ¬ z < 3 := by omega
  simp only [node, if_neg hNot] at hOpt
  have hPair :
      ((F.signature i).1,
        (fun s : FiniteTwoSplitIndex A n =>
          if s.val.val < z then (F.signature i).2 s else false)) =
      ((F.signature j).1,
        (fun s : FiniteTwoSplitIndex A n =>
          if s.val.val < z then (F.signature j).2 s else false)) :=
    Option.some.inj hOpt
  injection hPair with hSign hMasked
  exact hSign

/-- Same node at level z remembers each source S2 bit whose
genuine split level is STRICTLY before z. -/
theorem s2_bit_eq_of_node_eq
    (F : FiniteSignRootedFlipFamily A n ι)
    (i j : ι) (z : Nat)
    (hz : 3 ≤ z)
    (h : F.node i z = F.node j z)
    (s : FiniteTwoSplitIndex A n)
    (hsz : s.val.val < z) :
    (F.signature i).2 s = (F.signature j).2 s := by
  have hOpt := congrArg
    (fun v : FiniteSignRootedNode A n => v.2) h
  have hNot : ¬ z < 3 := by omega
  simp only [node, if_neg hNot] at hOpt
  have hPair :
      ((F.signature i).1,
        (fun q : FiniteTwoSplitIndex A n =>
          if q.val.val < z then (F.signature i).2 q else false)) =
      ((F.signature j).1,
        (fun q : FiniteTwoSplitIndex A n =>
          if q.val.val < z then (F.signature j).2 q else false)) :=
    Option.some.inj hOpt
  have hFun := congrArg Prod.snd hPair
  have hS := congrFun hFun s
  simpa only [if_pos hsz] using hS

/-- Equality at any terminal level z forces equality of all
earlier nodes. This is the tree property that the old
flip-prefix coding also had, now with the root sign present. -/
theorem node_prefix_eq_of_terminal_eq
    (F : FiniteSignRootedFlipFamily A n ι)
    (i j : ι) (m z : Nat)
    (hmz : m ≤ z)
    (hterminal : F.node i z = F.node j z) :
    F.node i m = F.node j m := by
  by_cases hm3 : m < 3
  · exact F.node_markers_shared i j m hm3
  have hmge : 3 ≤ m := by omega
  have hzge : 3 ≤ z := by omega
  have hSign := F.sign_eq_of_node_eq i j z hzge hterminal
  apply Prod.ext
  · rfl
  · have hNot : ¬ m < 3 := by omega
    simp only [node, if_neg hNot]
    apply congrArg some
    apply Prod.ext
    · exact hSign
    · funext s
      by_cases hsm : s.val.val < m
      · have hsz : s.val.val < z := lt_of_lt_of_le hsm hmz
        have hS := F.s2_bit_eq_of_node_eq i j z hzge hterminal s hsz
        simpa only [if_pos hsm] using hS
      · simp only [if_neg hsm]

/-- If two terminal nodes coincide, then the corresponding
bounded source triples ending at z have equal edge bits
(including nonedges). Crucially marker-one changes are
not hidden as future one-split choices. -/
theorem edge_agree_of_shared_terminal_node
    (F : FiniteSignRootedFlipFamily A n ι)
    (i j : ι)
    (x y z : Nat) (hxy : x < y) (hyz : y < z)
    (hzn : z < n)
    (hnode : F.node i z = F.node j z) :
    (F.graph i).edge x y z ↔ (F.graph j).edge x y z := by
  classical
  by_cases hz3 : 3 ≤ z
  · by_cases hPair : FiniteSourceHasLeafPair A n
    · let r := (finiteSourceLeafReference A n).1
      let t := (finiteSourceLeafReference A n).2
      obtain ⟨hrt,htn,hr,ht⟩ :=
        finiteSourceLeafReference_spec A n hPair
      have hMarkerDec : decide ((F.graph i).edge 1 r t) =
          decide ((F.graph j).edge 1 r t) := by
        have hSign := F.sign_eq_of_node_eq i j z hz3 hnode
        change decide ((F.graph i).edge 1 r t) =
          decide ((F.graph j).edge 1 r t) at hSign
        exact hSign
      have hReference :
          (F.graph i).edge 1 r t ↔ (F.graph j).edge 1 r t := by
        by_cases hL : (F.graph i).edge 1 r t <;>
          by_cases hR : (F.graph j).edge 1 r t <;>
          simp_all
      have hEarlier :
          ∀ s : Nat, IsTwoSplit A s → s < z →
            ∃ a b c d : Nat,
              a < b ∧ c < d ∧ b < n ∧ d < n ∧
              IsLeaf A a ∧ IsLeaf A b ∧
              IsLeaf A c ∧ IsLeaf A d ∧
              s < a ∧ s < c ∧
              A.twoMeetLevel a b c d = s ∧
              ((F.graph i).edge s a b ↔ (F.graph j).edge s a b) := by
        intro s hs hsz
        let idx : FiniteTwoSplitIndex A n :=
          ⟨⟨s, F.source.prediary.twoSplit_lt s hs⟩,hs⟩
        let W := finiteSelectedS2Witness F.source idx
        have hb := F.s2_bit_eq_of_node_eq i j z hz3
          hnode idx hsz
        have hBits :
            decide ((F.graph i).edge s W.a W.b) =
              decide ((F.graph j).edge s W.a W.b) := by
          change decide ((F.graph i).edge s W.a W.b) =
            decide ((F.graph j).edge s W.a W.b) at hb
          exact hb
        have hInc :
            (F.graph i).edge s W.a W.b ↔
              (F.graph j).edge s W.a W.b := by
          by_cases hi : (F.graph i).edge s W.a W.b <;>
            by_cases hj : (F.graph j).edge s W.a W.b <;>
            simp_all
        exact ⟨W.a,W.b,W.c,W.d,
          W.hab,W.hcd,W.hbn,W.hdn,
          W.ha,W.hb,W.hc,W.hd,W.hsa,W.hsc,W.hMeet,hInc⟩
      exact finite_two_flips_edges_agree_before_cut
        (F.flip i) (F.flip j) r t z
        hrt htn hr ht hReference hEarlier
        x y z hxy hyz hzn (by omega)
    · have hGraph :
          F.graph i = F.graph j :=
        finite_two_flips_eq_of_no_source_leaf_pair
          F.source (F.flip i) (F.flip j) hPair
      rw [hGraph]
  · have hNotI : ¬ (F.graph i).edge x y z := by
      intro hEdge
      have hzBound :=
        ((F.flip i).target_diary.prediary.frame.edge_support
          x y z hEdge).2.2.1
      omega
    have hNotJ : ¬ (F.graph j).edge x y z := by
      intro hEdge
      have hzBound :=
        ((F.flip j).target_diary.prediary.frame.edge_support
          x y z hEdge).2.2.1
      omega
    exact iff_of_false hNotI hNotJ

/-- The raw relational union of all source flip branches.
Only increasing actual source triples below the finite bound
are used; no invented cross-branch edge is present. -/
def rawAmalgam
    (F : FiniteSignRootedFlipFamily A n ι) :
    Ordered3Graph (FiniteSignRootedNode A n) where
  edge X Y Z :=
    ∃ (i : ι) (x y z : Nat),
      x < y ∧ y < z ∧ z < n ∧
      F.node i x = X ∧ F.node i y = Y ∧ F.node i z = Z ∧
      (F.graph i).edge x y z

/-- Every original finite source flip is an INDUCED branch of
the actual sign-rooted raw union. Even if another branch
witnesses a hyperedge between the same nodes, terminal
prefix equality forces the same edge bit on this branch. -/
theorem rawAmalgam_edge_iff
    (F : FiniteSignRootedFlipFamily A n ι)
    (i : ι) (x y z : Nat)
    (hxy : x < y) (hyz : y < z) (hzn : z < n) :
    (F.rawAmalgam).edge
      (F.node i x) (F.node i y) (F.node i z) ↔
      (F.graph i).edge x y z := by
  constructor
  · rintro ⟨j, xx, yy, zz, hxx, hyy, hzz,
      hx, hy, hz, hE⟩
    have ex : xx = x := by
      have hh := congrArg Prod.fst hx
      simpa only [node_level] using hh
    have ey : yy = y := by
      have hh := congrArg Prod.fst hy
      simpa only [node_level] using hh
    have ez : zz = z := by
      have hh := congrArg Prod.fst hz
      simpa only [node_level] using hh
    subst xx
    subst yy
    subst zz
    exact (F.edge_agree_of_shared_terminal_node
      j i x y z hxy hyz hzn hz).mp hE
  · intro hE
    exact ⟨i,x,y,z,hxy,hyz,hzn,rfl,rfl,rfl,hE⟩

end FiniteSignRootedFlipFamily
end DiaryLeafPriority
end ThreeUniformDiaries
