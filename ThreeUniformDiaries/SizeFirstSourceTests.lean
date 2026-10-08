import ThreeUniformDiaries.BranchCutBoundary
import ThreeUniformDiaries.RelativeLevelPopulation
import ThreeUniformDiaries.SizeFirstEnumeration

/-!
# Source-side type agreement under a size-first K_I presentation

The relative branch hypergraph is countable with finite nonempty
levels. In a length-first enumeration, target image comparisons below
the index of a branch vertex can include unrelated K_I nodes at the
same finite length. BranchCutBoundary proves that these extra tests
vanish.

This file separates that source-side fact from the still-to-be-built
length-first enumeration. It does not assert that an arbitrary
bijection satisfying the displayed length monotonicity has already
been constructed.
-/

namespace ThreeUniformDiaries

/-- A presentation of the relative branch hypergraph by natural
indices ordered nondecreasingly by the number of ordinary vertices. -/
structure SizeFirstBranchPresentation {n : Nat} (I : EnumNode n) where
  code : Nat ≃ RelativeBranchNode I
  length_mono : Monotone (fun i : Nat => (code i).val.last)

namespace SizeFirstBranchPresentation

variable {n : Nat} {I : EnumNode n} (E : SizeFirstBranchPresentation I)

/-- The indexed source hypergraph corresponding to the presentation. -/
def graph : Ordered3Graph Nat where
  edge a b c := (relativeBranchGraph I).edge (E.code a) (E.code b) (E.code c)

/-- The position of the finite prefix H|_(v+1) in the presentation. -/
noncomputable def branchIndex
    (H : Ordered3Graph Nat) (hI : H.initialSegment n = I) (v : Nat) :
    Nat := E.code.symm (H.relativeBranchNode I hI v)

@[simp] theorem code_branchIndex
    (H : Ordered3Graph Nat) (hI : H.initialSegment n = I) (v : Nat) :
    E.code (E.branchIndex H hI v) = H.relativeBranchNode I hI v := by
  simp [branchIndex]

@[simp] theorem branchIndex_last
    (H : Ordered3Graph Nat) (hI : H.initialSegment n = I) (v : Nat) :
    (E.code (E.branchIndex H hI v)).val.last = v := by
  rw [E.code_branchIndex H hI v]
  rfl

/-- Original branch order remains increasing in any size-first presentation. -/
theorem branchIndex_strictMono
    (H : Ordered3Graph Nat) (hI : H.initialSegment n = I) :
    StrictMono (E.branchIndex H hI) := by
  intro u v huv
  by_contra hbad
  have hle : E.branchIndex H hI v ≤ E.branchIndex H hI u :=
    Nat.le_of_not_gt hbad
  have hlen := E.length_mono hle
  have hu : (E.code (E.branchIndex H hI u)).val.last = u :=
    E.branchIndex_last H hI u
  have hv : (E.code (E.branchIndex H hI v)).val.last = v :=
    E.branchIndex_last H hI v
  change (E.code (E.branchIndex H hI v)).val.last ≤
    (E.code (E.branchIndex H hI u)).val.last at hlen
  rw [hu, hv] at hlen
  omega

/-- The induced source K_I graph agrees with H on every increasing
triple of its canonical branch indices. -/
theorem graph_branch_edge_iff
    (H : Ordered3Graph Nat) (hI : H.initialSegment n = I)
    {u v w : Nat} (huv : u < v) (hvw : v < w) :
    E.graph.edge (E.branchIndex H hI u)
      (E.branchIndex H hI v) (E.branchIndex H hI w) ↔
        H.edge u v w := by
  change (relativeBranchGraph I).edge
    (E.code (E.branchIndex H hI u))
    (E.code (E.branchIndex H hI v))
    (E.code (E.branchIndex H hI w)) ↔ H.edge u v w
  rw [E.code_branchIndex H hI u, E.code_branchIndex H hI v,
    E.code_branchIndex H hI w]
  exact H.relativeBranchNode_edge_iff I hI huv hvw

/-- The source indexed hypergraph's singleton tests strictly before a
branch cut agree whenever the original H types agree through that cut. -/
theorem source_oneType_test_below_branch_cut
    (H : Ordered3Graph Nat) (hI : H.initialSegment n = I)
    (w u v : Nat) (hwu : w ≤ u) (hwv : w ≤ v)
    (hsame : H.SameOneTypeBelow w u v)
    (a b : Nat) (hab : a < b)
    (hbelow : b < E.branchIndex H hI w) :
    E.graph.edge a b (E.branchIndex H hI u) ↔
      E.graph.edge a b (E.branchIndex H hI v) := by
  have hbcut : (E.code b).val.last ≤ w := by
    have h := E.length_mono (Nat.le_of_lt hbelow)
    change (E.code b).val.last ≤
      (E.code (E.branchIndex H hI w)).val.last at h
    rw [E.branchIndex_last H hI w] at h
    exact h
  by_cases hlength : (E.code a).val.last < (E.code b).val.last
  · have hwrong :
        (E.code b).val.last = w →
          (E.code b).val ≠ H.branchNode w := by
      intro hbEq hn
      have hnode : E.code b = H.relativeBranchNode I hI w :=
        Subtype.ext hn
      have hindex : b = E.branchIndex H hI w := by
        apply E.code.injective
        simpa using hnode
      exact (Nat.ne_of_lt hbelow) hindex
    have h := H.relativeBranch_sameOneType_at_boundary
      I hI w u v hwu hwv hsame
      (E.code a) (E.code b) hlength hbcut hwrong
    simpa only [graph, code_branchIndex] using h
  · have hleft :
        ¬ E.graph.edge a b (E.branchIndex H hI u) := by
      intro hed
      exact hlength hed.1
    have hright :
        ¬ E.graph.edge a b (E.branchIndex H hI v) := by
      intro hed
      exact hlength hed.1
    exact iff_of_false hleft hright

/-- The analogous auxiliary comparison includes all source candidates
before the indexed branch cut, including same-length non-prefix nodes. -/
theorem source_auxType_test_below_branch_cut
    (H : Ordered3Graph Nat) (hI : H.initialSegment n = I)
    (w u₀ u₁ v₀ v₁ : Nat)
    (hwu : w ≤ u₀) (hu : u₀ < u₁)
    (hwv : w ≤ v₀) (hv : v₀ < v₁)
    (hsame : H.SameAuxTypeBelow w u₀ u₁ v₀ v₁)
    (a : Nat) (hbelow : a < E.branchIndex H hI w) :
    E.graph.edge a
      (E.branchIndex H hI u₀) (E.branchIndex H hI u₁) ↔
    E.graph.edge a
      (E.branchIndex H hI v₀) (E.branchIndex H hI v₁) := by
  have hacut : (E.code a).val.last ≤ w := by
    have h := E.length_mono (Nat.le_of_lt hbelow)
    change (E.code a).val.last ≤
      (E.code (E.branchIndex H hI w)).val.last at h
    rw [E.branchIndex_last H hI w] at h
    exact h
  have hwrong :
      (E.code a).val.last = w →
        (E.code a).val ≠ H.branchNode w := by
    intro haEq hn
    have hnode : E.code a = H.relativeBranchNode I hI w :=
      Subtype.ext hn
    have hindex : a = E.branchIndex H hI w := by
      apply E.code.injective
      simpa using hnode
    exact (Nat.ne_of_lt hbelow) hindex
  have h := H.relativeBranch_sameAuxType_at_boundary
    I hI w u₀ u₁ v₀ v₁ hwu hu hwv hv hsame
    (E.code a) hacut hwrong
  simpa only [graph, code_branchIndex] using h


/-- The original singleton-type agreement is preserved by all
selected tests before its *indexed* K_I branch cut, not merely before
the original finite source length. -/
theorem source_oneAgreement_at_index
    (H : Ordered3Graph Nat) (hI : H.initialSegment n = I)
    (w u v : Nat) (hwu : w ≤ u) (hwv : w ≤ v)
    (hsame : H.SameOneTypeBelow w u v) :
    E.graph.SameOneTypeBelow (E.branchIndex H hI w)
      (E.branchIndex H hI u) (E.branchIndex H hI v) := by
  intro a b hab hb
  exact E.source_oneType_test_below_branch_cut
    H hI w u v hwu hwv hsame a b hab hb

/-- Auxiliary type agreement is likewise preserved at the actual
index of a canonical branch cut in the size-first K_I source. -/
theorem source_auxAgreement_at_index
    (H : Ordered3Graph Nat) (hI : H.initialSegment n = I)
    (w u₀ u₁ v₀ v₁ : Nat)
    (hwu : w ≤ u₀) (hu : u₀ < u₁)
    (hwv : w ≤ v₀) (hv : v₀ < v₁)
    (hsame : H.SameAuxTypeBelow w u₀ u₁ v₀ v₁) :
    E.graph.SameAuxTypeBelow (E.branchIndex H hI w)
      (E.branchIndex H hI u₀) (E.branchIndex H hI u₁)
      (E.branchIndex H hI v₀) (E.branchIndex H hI v₁) := by
  intro a ha
  exact E.source_auxType_test_below_branch_cut
    H hI w u₀ u₁ v₀ v₁ hwu hu hwv hv hsame a ha


/-- A size-first enumeration begins with precisely the unique finite
prefixes of I. This uses monotonicity of lengths, nonemptiness of each
level and uniqueness of the levels strictly below |I|. -/
theorem initial_source_nodes
    (k : Nat) (hk : k < n) :
    E.code k = relativeBranchCanonical I k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      let C := relativeBranchCanonical I k
      let j := E.code.symm C
      have hcanon : E.code j = C := E.code.apply_symm_apply C
      have hj : k ≤ j := by
        by_contra hnkj
        have hjk : j < k := Nat.lt_of_not_ge hnkj
        have hjn : j < n := lt_trans hjk hk
        have hprev : E.code j = relativeBranchCanonical I j :=
          ih j hjk hjn
        have heq : relativeBranchCanonical I j =
            relativeBranchCanonical I k := by
          calc
            relativeBranchCanonical I j = E.code j := hprev.symm
            _ = C := hcanon
            _ = relativeBranchCanonical I k := rfl
        have hlast := congrArg
          (fun A : RelativeBranchNode I => A.val.last) heq
        simp at hlast
        omega
      have hle : (E.code k).val.last ≤ k := by
        have hm := E.length_mono hj
        change (E.code k).val.last ≤ (E.code j).val.last at hm
        rw [hcanon] at hm
        simpa [C] using hm
      have hge : k ≤ (E.code k).val.last := by
        by_contra hnot
        let ell := (E.code k).val.last
        have hell : ell < k := Nat.lt_of_not_ge hnot
        have helln : ell < n := lt_trans hell hk
        have heq : E.code k = relativeBranchCanonical I ell :=
          relativeBranch_initial_unique I ell helln (E.code k) rfl
        have hprev : E.code ell = relativeBranchCanonical I ell :=
          ih ell hell helln
        have hindices : k = ell :=
          E.code.injective (heq.trans hprev.symm)
        omega
      have hlast : (E.code k).val.last = k := Nat.le_antisymm hle hge
      exact relativeBranch_initial_unique I k hk (E.code k) hlast

end SizeFirstBranchPresentation

/-- The concrete size-first presentation of the relative branch
hypergraph, constructed from its increasing numerical-code order. -/
noncomputable def canonicalSizeFirstBranchPresentation
    {n : Nat} (I : EnumNode n) : SizeFirstBranchPresentation I where
  code := relativeBranchSizeFirstEquiv I
  length_mono := relativeBranchSizeFirst_length_mono I

/-- In particular its first |I| positions are the prescribed initial
prefixes of I, with no intervening nodes. -/
theorem canonicalSizeFirst_initial_node
    {n : Nat} (I : EnumNode n) (k : Nat) (hk : k < n) :
    (canonicalSizeFirstBranchPresentation I).code k =
      relativeBranchCanonical I k :=
  (canonicalSizeFirstBranchPresentation I).initial_source_nodes k hk

end ThreeUniformDiaries
