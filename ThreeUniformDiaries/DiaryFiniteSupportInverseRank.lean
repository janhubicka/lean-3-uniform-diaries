import ThreeUniformDiaries.DiaryFiniteLeafMeetCompleteReduct
import ThreeUniformDiaries.DiaryFiniteMeetEmbedding

/-!
# Canonical inverse indices of finite induced supports

The sorted enumeration of a finite support S is inverted on S,
and extended to a globally strictly increasing map of Nat by
placing the unused source tail beyond S.card. This supplies the
actual finite-copy map needed for numerical-meet factorisation.

No arbitrary old type-agreement equivalence is assumed: finite
compression can delete tests. The first-disagreement witnesses
must be handled separately for the numerical-meet fields.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The index of a supported old vertex in the increasing enumeration.
Outside the support we use the harmless index zero. -/
noncomputable def finiteSupportRank (S : Finset Nat) (x : Nat) : Nat := by
  classical
  exact if hx : x ∈ S then
    (finiteSupportIndex_surjective_on S x hx).choose else 0

/-- The actual old vertex is recovered from its finite rank. -/
theorem finiteSupportRank_spec
    (S : Finset Nat) (x : Nat) (hx : x ∈ S) :
    finiteSupportRank S x < S.card ∧
      finiteSupportIndex S (finiteSupportRank S x) = x := by
  classical
  simp only [finiteSupportRank, dif_pos hx]
  exact (finiteSupportIndex_surjective_on S x hx).choose_spec

/-- The rank of the vertex at index i is literally i. -/
theorem finiteSupportRank_of_index
    (S : Finset Nat) (i : Nat) (hi : i < S.card) :
    finiteSupportRank S (finiteSupportIndex S i) = i := by
  have hx : finiteSupportIndex S i ∈ S :=
    finiteSupportIndex_mem S i hi
  have hspec := finiteSupportRank_spec S _ hx
  let j := finiteSupportRank S (finiteSupportIndex S i)
  have hji : finiteSupportIndex S j = finiteSupportIndex S i := hspec.2
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hjiLt
  · have hstrict := finiteSupportIndex_strictMono S j i hij hi
    omega
  · have hstrict := finiteSupportIndex_strictMono S i j hjiLt hspec.1
    omega

/-- The rank is strictly order preserving on the selected set. -/
theorem finiteSupportRank_lt
    (S : Finset Nat) {x y : Nat}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) :
    finiteSupportRank S x < finiteSupportRank S y := by
  have hxs := finiteSupportRank_spec S x hx
  have hys := finiteSupportRank_spec S y hy
  by_contra hnot
  have hle : finiteSupportRank S y ≤ finiteSupportRank S x := by omega
  have hBack := finiteSupportIndex_mono_below S
    (finiteSupportRank S y) (finiteSupportRank S x)
    hys.1 hxs.1 hle
  rw [hys.2,hxs.2] at hBack
  omega

/-- A source finite prefix is mapped to its selected target ranks.
The dummy source tail is sent to fresh consecutive indices >= S.card.
This yields a genuinely strictly increasing map on ALL naturals. -/
noncomputable def finiteSupportLift
    (S : Finset Nat) (n : Nat) (f : Nat → Nat)
    (u : Nat) : Nat :=
  if u < n then finiteSupportRank S (f u)
  else S.card + (u - n)

/-- Selected source vertices map to their actual finite ranks. -/
theorem finiteSupportLift_of_lt
    (S : Finset Nat) (n : Nat) (f : Nat → Nat)
    (u : Nat) (hu : u < n) :
    finiteSupportLift S n f u = finiteSupportRank S (f u) := by
  simp only [finiteSupportLift, if_pos hu]

/-- Every selected finite source vertex maps inside the target
finite bound and is re-enumerated to its precise old image. -/
theorem finiteSupportLift_spec
    (S : Finset Nat) (n : Nat) (f : Nat → Nat)
    (hRange : ∀ u, u < n → f u ∈ S)
    (u : Nat) (hu : u < n) :
    finiteSupportLift S n f u < S.card ∧
      finiteSupportIndex S (finiteSupportLift S n f u) = f u := by
  rw [finiteSupportLift_of_lt S n f u hu]
  exact finiteSupportRank_spec S (f u) (hRange u hu)

/-- The total lift is strictly increasing whenever the source
embedding is increasing and its finite domain lies in S. -/
theorem finiteSupportLift_strictMono
    (S : Finset Nat) (n : Nat) (f : Nat → Nat)
    (hf : StrictMono f)
    (hRange : ∀ u, u < n → f u ∈ S) :
    StrictMono (finiteSupportLift S n f) := by
  apply strictMono_nat_of_lt_succ
  intro u
  by_cases hs : u + 1 < n
  · have hu : u < n := by omega
    have huRange := hRange u hu
    have hsRange := hRange (u + 1) hs
    have hstrict := finiteSupportRank_lt
      S huRange hsRange (hf (by omega : u < u + 1))
    simpa only [finiteSupportLift, if_pos hu, if_pos hs] using hstrict
  · by_cases hu : u < n
    · have hbound := (finiteSupportRank_spec S (f u) (hRange u hu)).1
      simp only [finiteSupportLift, if_pos hu, if_neg hs]
      omega
    · have hnext : ¬ u + 1 < n := by omega
      simp only [finiteSupportLift, if_neg hu, if_neg hnext]
      omega

/-- A marker kept in its original index is also fixed by rank. -/
theorem finiteSupportRank_marker
    (S : Finset Nat)
    (h0 : 0 ∈ S) (h1 : 1 ∈ S) (h2 : 2 ∈ S) :
    finiteSupportRank S 0 = 0 ∧
      finiteSupportRank S 1 = 1 ∧
      finiteSupportRank S 2 = 2 := by
  obtain ⟨hcard,hZero,hOne,hTwo⟩ :=
    finiteSupportIndex_initial_markers S h0 h1 h2
  exact ⟨by simpa only [hZero] using finiteSupportRank_of_index S 0 (by omega),
    by simpa only [hOne] using finiteSupportRank_of_index S 1 (by omega),
    by simpa only [hTwo] using finiteSupportRank_of_index S 2 (by omega)⟩

/-- A marker-fixing finite embedding still fixes 0,1,2 after
the support is reindexed. -/
theorem finiteSupportLift_markers
    (S : Finset Nat) (n : Nat) (f : Nat → Nat)
    (hn : 3 ≤ n)
    (h0 : 0 ∈ S) (h1 : 1 ∈ S) (h2 : 2 ∈ S)
    (hf0 : f 0 = 0) (hf1 : f 1 = 1) (hf2 : f 2 = 2) :
    finiteSupportLift S n f 0 = 0 ∧
      finiteSupportLift S n f 1 = 1 ∧
      finiteSupportLift S n f 2 = 2 := by
  obtain ⟨hZero,hOne,hTwo⟩ := finiteSupportRank_marker S h0 h1 h2
  constructor
  · simp only [finiteSupportLift_of_lt S n f 0 (by omega),hf0,hZero]
  constructor
  · simp only [finiteSupportLift_of_lt S n f 1 (by omega),hf1,hOne]
  · simp only [finiteSupportLift_of_lt S n f 2 (by omega),hf2,hTwo]

end DiaryLeafPriority
end ThreeUniformDiaries
