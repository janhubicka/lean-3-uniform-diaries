import ThreeUniformDiaries.DiaryFiniteSignRootedRawAmalgam
import ThreeUniformDiaries.DiaryFiniteCanonicalSourceFlipOrbit

/-!
# The actual finite sign-rooted raw tree of ALL source diary flips

The preceding raw sign-rooted branch amalgam is deliberately
parametric in a family of genuine finite flips. Here it is
instantiated with exactly the CANONICAL finite source flip orbit,
which contains every genuine labelled source flip exactly once.

The index is the subtype of canonical finite edge codes,
rather than the redundant raw Boolean cube. Its graph is the
decoded finite V/E/S diary, and its flip certificate is
obtained directly from genuine canonical orbit membership.

The actual collection of sign-rooted nodes on levels [0,n)
is the IMAGE of a finite product of this orbit with Fin n.
Hence it is a concrete finite carrier, every genuine source
flip occurs as an induced branch of its raw ternary relation,
and the total number of branch nodes is finite.

The raw relation on those nodes is NOT yet a complete
finite pre-diary: ordering distinct nodes on the same source
level, cross-branch V3 Devlin markers, positive-class
V1/V2 coherence after completion, and mixed-meet protection
remain separate mathematical obligations.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Index the entire genuine finite source flip orbit by
canonical edge codes, with no redundant raw bits. -/
abbrev FiniteCanonicalFlipIndex (A : Ordered3Graph Nat) (n : Nat) :=
  {c : FiniteDiaryEdgeCode n //
    c ∈ finiteCanonicalSourceFlipCodes A n}

/-- One concrete family containing every genuine source flip,
with its whole bounded V/E/S diary certificate. -/
noncomputable def finiteCanonicalSignRootedFamily
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n) :
    FiniteSignRootedFlipFamily A n (FiniteCanonicalFlipIndex A n) where
  source := DA
  graph := fun c => finiteDiaryCodeGraph n c.val
  flip := by
    intro c
    have hc :
        c.val ∈ finiteSourceFlipCodes A n :=
      ((mem_finiteCanonicalSourceFlipCodes_iff A n c.val).mp
        c.property).1
    exact (mem_finiteSourceFlipCodes_iff A n c.val).mp hc

/-- Every real finite diary flip appears literally among the
source branches of the canonical sign-rooted family. -/
theorem finiteCanonicalSignRootedFamily_complete
    {A P : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (FP : FiniteDiaryFlip A P n) :
    ∃ c : FiniteCanonicalFlipIndex A n,
      (finiteCanonicalSignRootedFamily DA).graph c = P := by
  obtain ⟨code,hCode,hGraph⟩ :=
    finiteCanonicalSourceFlipCodes_complete FP
  exact ⟨⟨code,hCode⟩,hGraph⟩

/-- A genuine finite source flip is an INDUCED branch of the
canonical raw sign-rooted amalgam, including all nonedges
between its original finite vertices. -/
theorem finiteCanonicalSignRootedFamily_all_flips_induced
    {A P : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (FP : FiniteDiaryFlip A P n) :
    ∃ c : FiniteCanonicalFlipIndex A n,
      (finiteCanonicalSignRootedFamily DA).graph c = P ∧
      (∀ x y z : Nat, x < y → y < z → z < n →
        ((finiteCanonicalSignRootedFamily DA).rawAmalgam).edge
          ((finiteCanonicalSignRootedFamily DA).node c x)
          ((finiteCanonicalSignRootedFamily DA).node c y)
          ((finiteCanonicalSignRootedFamily DA).node c z) ↔
          P.edge x y z) := by
  obtain ⟨c,hGraph⟩ :=
    finiteCanonicalSignRootedFamily_complete DA FP
  refine ⟨c,hGraph,?_⟩
  intro x y z hxy hyz hzn
  exact ((finiteCanonicalSignRootedFamily DA).rawAmalgam_edge_iff
    c x y z hxy hyz hzn).trans
    (by rw [hGraph])

/-- The ACTUAL raw carrier is a finite set of sign-rooted nodes:
one node for each realised canonical flip at each source
level, with equal prefixes identified by Finset.image. -/
noncomputable def finiteCanonicalSignRootedNodeSet
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n) :
    Finset (FiniteSignRootedNode A n) := by
  classical
  exact (Finset.univ :
    Finset (FiniteCanonicalFlipIndex A n × Fin n)).image
      (fun p => (finiteCanonicalSignRootedFamily DA).node
        p.1 p.2.val)

/-- Every original source branch vertex within its bounded
diary support belongs to the finite sign-rooted carrier. -/
theorem finiteCanonicalSignRootedNodeSet_contains
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (c : FiniteCanonicalFlipIndex A n)
    (z : Nat) (hzn : z < n) :
    (finiteCanonicalSignRootedFamily DA).node c z ∈
      finiteCanonicalSignRootedNodeSet DA := by
  classical
  unfold finiteCanonicalSignRootedNodeSet
  apply Finset.mem_image.mpr
  exact ⟨(c, ⟨z,hzn⟩), Finset.mem_univ _, rfl⟩

/-- The number of realised canonical source flip BRANCHES is
bounded unconditionally by one global orientation bit and
one E3 bit for each genuine source 2-split. -/
theorem finiteCanonicalSignRootedFamily_branch_count_bound
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n) :
    Fintype.card (FiniteCanonicalFlipIndex A n) ≤
      2 ^ (finiteTwoSplitCount A n + 1) :=
  finiteCanonicalSourceFlipOrbit_card_bound_unconditional DA

end DiaryLeafPriority
end ThreeUniformDiaries
