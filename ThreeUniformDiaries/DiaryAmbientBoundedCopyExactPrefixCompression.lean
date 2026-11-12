import ThreeUniformDiaries.DiaryFiniteLeafSupportCoversPrefix
import ThreeUniformDiaries.DiaryFiniteProtectedFactorization
import ThreeUniformDiaries.DiaryFiniteBoundedUniversality
import ThreeUniformDiaries.DiaryNoLiteralFiniteFullDiaryEndExtension

/-!
# Track B: finite full compression preserves a supplied bounded ambient copy literally

Take a supplied genuine finite all-numerical-meet embedding f:A→G
into an ACTUAL countable full RoleDiary G. Assume all old finite
source vertices have known numerical images <p. Then a genuine
finite full leaf-meet compression of G can simultaneously retain:
* the WHOLE old ambient prefix [0,p) literally, with all edges and
  nonedges;
* every selected old source image f(u) at its exact old numerical
  position (not merely as some independently re-chosen copy);
* the entire induced, marker-role and all-mixed-meet embedding data;
* at least one genuine terminal leaf beyond ALL the old images.

The proof uses the previously verified finite full support containing
the slightly longer ambient prefix [0,p+1), and the rank-fixation
lemma for any complete numerical prefix. Factor the already supplied
finite source embedding through exactly that finite support; rank
fixation identifies the factor map with f on the ENTIRE true source
frame. The terminal vertex is a leaf by the finite witness axioms.

This is NOT a construction of an ambient countable protected
extension, which remains the substantive OPEN relative absorber step.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Any supplied protected finite image lying numerically below p
can be compressed into a genuine finite full diary WITHOUT CHANGING
ANY OF ITS NUMERICAL IMAGE RANKS, while leaving a genuine new leaf
at the end of the finite target.

The total Nat map g is a standard finite-source extension; on
every genuine vertex u<n it agrees literally with the given f.
The output is also an induced literal copy of the ambient first
p vertices, including nonedge reflection. -/
theorem FiniteMeetEmbedding.exists_finiteFull_compression_preserving_bounded_image
    {A G : Ordered3Graph Nat} {n : Nat} {f : Nat → Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (hn : 4 ≤ n)
    (DG : RoleDiary G)
    (E : FiniteMeetEmbedding A G n f)
    (p : Nat)
    (hOldImage : ∀ u : Nat, u < n → f u < p) :
    ∃ (C : Ordered3Graph Nat) (m : Nat) (g : Nat → Nat),
      FiniteRoleDiaryBlock C m ∧
      p < m ∧
      FiniteBoundedMeetEmbedding A C n m g ∧
      (∀ u : Nat, u < n → g u = f u) ∧
      (∀ a b c : Nat, a < b → b < c → c < p →
        (C.edge a b c ↔ G.edge a b c)) ∧
      (IsLeaf C (m-1) ∧
        ∀ u : Nat, u < n → g u < m-1) := by
  classical
  obtain ⟨L,hLeaves,hFinite,hKeep⟩ :=
    DG.exists_finite_full_diary_retaining_prefix (p+1)
  let S : Finset Nat := finiteLeafMeetSupport G L
  let C : Ordered3Graph Nat := finiteSupportGraph G S
  let m : Nat := S.card
  let g : Nat → Nat := finiteSupportLift S n f
  have hPrefix : ∀ u : Nat, u < p+1 → u ∈ S := by
    intro u hu
    obtain ⟨hCard,hIndex⟩ := hKeep u hu
    have hMem := finiteSupportIndex_mem S u hCard
    rw [hIndex] at hMem
    exact hMem
  have hpM : p < m := (hKeep p (by omega)).1
  have hFrame : ∀ u : Nat, u < n → f u ∈ S := by
    intro u hu
    exact hPrefix (f u) (by have h := hOldImage u hu; omega)
  have hRank : ∀ u : Nat, u < p+1 →
      finiteSupportRank S u = u :=
    finiteSupportRank_fixed_prefix S (p+1) hPrefix
  have hG : FiniteMeetEmbedding A C n g :=
    E.through_finiteSupport DA S hFrame
  have hBound : ∀ u : Nat, u < n → g u < m := by
    intro u hu
    exact (finiteSupportLift_spec S n f hFrame u hu).1
  have hExact : ∀ u : Nat, u < n → g u = f u := by
    intro u hu
    have huR : f u < p+1 := by
      have h := hOldImage u hu
      omega
    change finiteSupportLift S n f u = f u
    rw [finiteSupportLift_of_lt S n f u hu]
    exact hRank (f u) huR
  have hEdges : ∀ a b c : Nat, a < b → b < c → c < p →
      (C.edge a b c ↔ G.edge a b c) := by
    intro a b c hab hbc hc
    have ha : a < p+1 := by omega
    have hb : b < p+1 := by omega
    have hcP : c < p+1 := by omega
    have hcM : c < m := (hKeep c hcP).1
    have haIndex := (hKeep a ha).2
    have hbIndex := (hKeep b hb).2
    have hcIndex := (hKeep c hcP).2
    have hEdge := finiteSupportGraph_edge_iff G S a b c hab hbc hcM
    change finiteSupportIndex S a = a at haIndex
    change finiteSupportIndex S b = b at hbIndex
    change finiteSupportIndex S c = c at hcIndex
    rw [haIndex, hbIndex, hcIndex] at hEdge
    exact hEdge
  have hFour : 4 ≤ m := by
    have hBound3 := hBound 3 (by omega : 3 < n)
    have hMono3 : g 2 < g 3 := hG.strictMono (by omega : 2 < 3)
    rw [hG.marker_two] at hMono3
    omega
  have hLast : IsLeaf C (m-1) := hFinite.last_is_leaf hFour
  have hBelowLast : ∀ u : Nat, u < n → g u < m-1 := by
    intro u hu
    have hLess : g u < p := by
      rw [hExact u hu]
      exact hOldImage u hu
    omega
  refine ⟨C,m,g,hFinite,hpM,⟨hG,hBound⟩,hExact,hEdges,hLast,hBelowLast⟩

end DiaryLeafPriority
end ThreeUniformDiaries
