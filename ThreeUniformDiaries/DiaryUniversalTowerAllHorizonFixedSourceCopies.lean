import ThreeUniformDiaries.DiaryUniversalTowerFixedSourceCopyStep

/-!
# Track B: one fixed finite source has a coherent copy at EVERY
# intermediate level of a prescribed finite target-flip horizon

The verified bounded absorber tower gives CHOSEN full-meet
embeddings e_(i,k):B_i -> B_(i+k). Here we prove their literal
semigroup law across every finite cut k+l.

Fix a single genuine finite source A already absorbed by B_i and
one genuine target flip T at stage B_(i+k). Pull T back to the
canonical genuine flip U of B_i, choose one copy A -> U from the
verified finite strong absorber theorem, and transport THIS SAME
copy through every intermediate pulled-back target flip.

For each j<=k, the resulting A -> T_j copy is bounded,
induced, and preserves ALL numerical meets. For j+l<=k, the copy
at level j+l is EXACTLY the selected transition e_(i+j,l)
composed with the copy at level j.

The target terminal flip T and a single finite source A are fixed
before selecting the base copy. The selected base copy still
depends on the entire terminal flip; no compatibility is obtained
when the terminal horizon grows or the source changes A_j -> A_(j+1).
The genuine countable-source flip property remains OPEN.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The actual chosen tower maps compose strictly, as FUNCTIONS
on all Nat, not merely up to agreement on bounded source frames.
This is a fact about the recursive definition and does not assert
that the maps are identity on their older target source ranks. -/
theorem universalStrongAbsorberTower_forwardMap_add
    (i k l : Nat) :
    universalStrongAbsorberTower_forwardMap i (k+l) =
      (fun u =>
        universalStrongAbsorberTower_forwardMap (i+k) l
          (universalStrongAbsorberTower_forwardMap i k u)) := by
  induction l with
  | zero =>
      simp only [Nat.add_zero,
        universalStrongAbsorberTower_forwardMap_zero]
  | succ l ih =>
      funext u
      calc
        universalStrongAbsorberTower_forwardMap i (k+(l+1)) u =
            universalStrongAbsorberTower_stepMap (i+(k+l))
              (universalStrongAbsorberTower_forwardMap i (k+l) u) := by
          rw [Nat.add_succ]
          rfl
        _ = universalStrongAbsorberTower_stepMap ((i+k)+l)
              (universalStrongAbsorberTower_forwardMap (i+k) l
                (universalStrongAbsorberTower_forwardMap i k u)) := by
          have hAt := congrFun ih u
          simpa only [Nat.add_assoc] using
            congrArg (universalStrongAbsorberTower_stepMap (i+(k+l))) hAt
        _ = universalStrongAbsorberTower_forwardMap (i+k) (l+1)
              (universalStrongAbsorberTower_forwardMap i k u) := by
          rfl

/-- Strict literal canonical flip pullback associativity at any
splitting of an arbitrary finite tower horizon. The target is any
raw ordered ternary graph. No genuine target flip is required for
this purely induced edge/nonedge equality. -/
theorem universalStrongAbsorberTower_forwardPullback_add
    (i j l : Nat) (T : Ordered3Graph Nat) :
    finiteDiaryPullbackGraph
      (finiteDiaryPullbackGraph T
        (universalStrongAbsorberTower (i+j)).bound
        (universalStrongAbsorberTower_forwardMap (i+j) l))
      (universalStrongAbsorberTower i).bound
      (universalStrongAbsorberTower_forwardMap i j) =
    finiteDiaryPullbackGraph T
      (universalStrongAbsorberTower i).bound
      (universalStrongAbsorberTower_forwardMap i (j+l)) := by
  have hComp := finiteDiaryPullbackGraph_comp_of_bounded (T := T)
    (universalStrongAbsorberTower_forwardMap_spec i j)
    (universalStrongAbsorberTower_forwardMap (i+j) l)
  have hAdd := universalStrongAbsorberTower_forwardMap_add i j l
  simpa only [← hAdd] using hComp

/-- An arbitrary ACTUAL finite flip T of B_(i+k) carries
a simultaneous coherent family of bounded full-meet copies of
one fixed finite source A, provided B_i already absorbs A.

The intermediate target flip T_j is the CANONICAL pullback of T
along the selected e_(i+j,k-j). One and the same h:A -> T_0
is chosen. All later source maps are the defined composites
e_(i,j) o h. No source map is chosen independently at any level. -/
theorem exists_compatible_fixed_source_copies_all_horizons
    {A : Ordered3Graph Nat} {n i k : Nat}
    (hAbs : AbsorbsEveryTargetFlipInside
      A (universalStrongAbsorberTower i).graph
      n (universalStrongAbsorberTower i).bound)
    (T : Ordered3Graph Nat)
    (FT : FiniteDiaryFlip
      (universalStrongAbsorberTower (i+k)).graph T
      (universalStrongAbsorberTower (i+k)).bound) :
    ∃ h : Nat → Nat,
      FiniteBoundedMeetEmbedding A
        (finiteDiaryPullbackGraph T
          (universalStrongAbsorberTower i).bound
          (universalStrongAbsorberTower_forwardMap i k))
        n (universalStrongAbsorberTower i).bound h ∧
      (∀ j : Nat, j ≤ k →
        FiniteBoundedMeetEmbedding A
          (finiteDiaryPullbackGraph T
            (universalStrongAbsorberTower (i+j)).bound
            (universalStrongAbsorberTower_forwardMap (i+j) (k-j)))
          n (universalStrongAbsorberTower (i+j)).bound
          (fun u =>
            universalStrongAbsorberTower_forwardMap i j (h u))) := by
  classical
  let U := finiteDiaryPullbackGraph T
    (universalStrongAbsorberTower i).bound
    (universalStrongAbsorberTower_forwardMap i k)
  have hU : FiniteDiaryFlip
      (universalStrongAbsorberTower i).graph U
      (universalStrongAbsorberTower i).bound :=
    universalStrongAbsorberTower_forwardPullback_is_flip i k T FT
  obtain ⟨h,Eh⟩ := hAbs U hU
  refine ⟨h,Eh,?_⟩
  intro j hj
  let Tj := finiteDiaryPullbackGraph T
    (universalStrongAbsorberTower (i+j)).bound
    (universalStrongAbsorberTower_forwardMap (i+j) (k-j))
  have hIndex : (i+j)+(k-j) = i+k := by omega
  have hTj : FiniteDiaryFlip
      (universalStrongAbsorberTower (i+j)).graph Tj
      (universalStrongAbsorberTower (i+j)).bound :=
    universalStrongAbsorberTower_forwardPullback_is_flip
      (i+j) (k-j) T (by simpa only [hIndex] using FT)
  have hJK : j+(k-j) = k := by omega
  have hPullback :
      finiteDiaryPullbackGraph Tj
        (universalStrongAbsorberTower i).bound
        (universalStrongAbsorberTower_forwardMap i j) = U := by
    simpa only [Tj,U,hJK] using
      universalStrongAbsorberTower_forwardPullback_add
        i j (k-j) T
  have hToTj :
      FiniteBoundedMeetEmbedding U Tj
        (universalStrongAbsorberTower i).bound
        (universalStrongAbsorberTower (i+j)).bound
        (universalStrongAbsorberTower_forwardMap i j) := by
    have h := finiteDiaryPullbackGraph_boundedEmbedding_into_targetFlip
      (universalStrongAbsorberTower i).diary
      (universalStrongAbsorberTower_forwardMap_spec i j) hTj
    rw [hPullback] at h
    exact h
  exact Eh.comp hToTj
    (universalStrongAbsorberTower i).diary.prediary.frame.length_ge_three

/-- The source maps in the preceding theorem form an exact
strictly compatible family under EVERY selected intermediate
tower map. This requires no separate choices of the source
maps and no additional diary assumptions. -/
theorem universalStrongAbsorberTower_fixed_source_map_coherent
    (i j l : Nat) (h : Nat → Nat) :
    (fun u => universalStrongAbsorberTower_forwardMap i (j+l) (h u)) =
      (fun u => universalStrongAbsorberTower_forwardMap (i+j) l
        (universalStrongAbsorberTower_forwardMap i j (h u))) := by
  funext u
  exact congrFun (universalStrongAbsorberTower_forwardMap_add i j l) (h u)

end DiaryLeafPriority
end ThreeUniformDiaries
