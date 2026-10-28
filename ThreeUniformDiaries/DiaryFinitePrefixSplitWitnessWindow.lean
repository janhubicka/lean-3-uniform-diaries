import ThreeUniformDiaries.DiaryFiniteCanonicalCausalCountableFlipOrbit

/-!
# Uniform finite witness windows inside a countable diary

The countable canonical-flip construction gives all source copies
in one diary, but a finite *initial segment* need not itself be a
finite diary: split vertices in the segment may have their genuine
V1/V2 witnesses later. This module extracts a SINGLE FINITE
witness window for all split vertices in any prescribed bounded
initial segment of any actual V/E pre-diary, including the
canonical source-flip orbit.

The distinction between the ORIGINAL cutoff k and the enlarged
witness cutoff K is essential. We do NOT assert that every newly
encountered split in [k,K) has witnesses before K. That would be
a finite closure theorem, not a consequence of ordinary finiteness.
No finite full diary or every-target-flip absorber is claimed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Uniformly bounded genuine split witness tuples for all split
vertices strictly before a prescribed cutoff. The bounds are on
all witness LEAVES, not just the old split vertices. -/
structure FinitePrefixSplitWitnesses
    (H : Ordered3Graph Nat) (k K : Nat) : Prop where
  one :
    ∀ s : Nat, s < k → IsOneSplit H s →
      ∃ a b : Nat,
        a < K ∧ b < K ∧
        IsLeaf H a ∧ IsLeaf H b ∧
        s < a ∧ s < b ∧ H.oneMeetLevel a b = s
  two :
    ∀ s : Nat, s < k → IsTwoSplit H s →
      ∃ a b c d : Nat,
        a < b ∧ c < d ∧
        a < K ∧ b < K ∧ c < K ∧ d < K ∧
        IsLeaf H a ∧ IsLeaf H b ∧
        IsLeaf H c ∧ IsLeaf H d ∧
        s < a ∧ s < c ∧
        H.twoMeetLevel a b c d = s

/-- Witness windows are monotone in their upper bound.
This does not change which OLD split vertices must be witnessed. -/
theorem FinitePrefixSplitWitnesses.mono
    {H : Ordered3Graph Nat} {k K L : Nat}
    (Q : FinitePrefixSplitWitnesses H k K)
    (hKL : K ≤ L) :
    FinitePrefixSplitWitnesses H k L := by
  refine ⟨?_,?_⟩
  · intro s hs hOne
    obtain ⟨a,b,ha,hb,hla,hlb,hsa,hsb,hMeet⟩ :=
      Q.one s hs hOne
    exact ⟨a,b,by omega,by omega,hla,hlb,hsa,hsb,hMeet⟩
  · intro s hs hTwo
    obtain ⟨a,b,c,d,hab,hcd,ha,hb,hc,hd,
      hla,hlb,hlc,hld,hsa,hsc,hMeet⟩ :=
        Q.two s hs hTwo
    exact ⟨a,b,c,d,hab,hcd,
      by omega,by omega,by omega,by omega,
      hla,hlb,hlc,hld,hsa,hsc,hMeet⟩

/-- For EVERY bounded prefix of a genuine countable V/E pre-diary,
one can find a common finite horizon containing witnesses for ALL
one- and two-splits OF THAT ORIGINAL PREFIX. No assumption of
global S1/S2 is used. The conclusion deliberately does not
require the newly extended horizon to be split-witness-closed. -/
theorem exists_finitePrefixSplitWitness_window
    {H : Ordered3Graph Nat}
    (P : RolePrediary H) (k : Nat) :
    ∃ K : Nat, k ≤ K ∧ FinitePrefixSplitWitnesses H k K := by
  classical
  induction k with
  | zero =>
      refine ⟨0,by omega,⟨?_,?_⟩⟩
      · intro s hs _
        omega
      · intro s hs _
        omega
  | succ k ih =>
      obtain ⟨K,hk,Q⟩ := ih
      have hOneBound :
          ∃ L : Nat, ∀ hs : IsOneSplit H k,
            ∃ a b : Nat,
              a < L ∧ b < L ∧
              IsLeaf H a ∧ IsLeaf H b ∧
              k < a ∧ k < b ∧ H.oneMeetLevel a b = k := by
        by_cases hs : IsOneSplit H k
        · obtain ⟨a,b,ha,hb,hka,hkb,hm⟩ :=
            P.one_split_witness k hs
          refine ⟨max a b + 1,?_⟩
          intro _
          exact ⟨a,b,by omega,by omega,ha,hb,hka,hkb,hm⟩
        · exact ⟨0,by intro bad; exact False.elim (hs bad)⟩
      have hTwoBound :
          ∃ L : Nat, ∀ hs : IsTwoSplit H k,
            ∃ a b c d : Nat,
              a < b ∧ c < d ∧
              a < L ∧ b < L ∧ c < L ∧ d < L ∧
              IsLeaf H a ∧ IsLeaf H b ∧
              IsLeaf H c ∧ IsLeaf H d ∧
              k < a ∧ k < c ∧
              H.twoMeetLevel a b c d = k := by
        by_cases hs : IsTwoSplit H k
        · obtain ⟨a,b,c,d,hab,hcd,ha,hb,hc,hd,hka,hkc,hm⟩ :=
            P.two_split_witness k hs
          refine ⟨max (max a b) (max c d) + 1,?_⟩
          intro _
          exact ⟨a,b,c,d,hab,hcd,
            by omega,by omega,by omega,by omega,
            ha,hb,hc,hd,hka,hkc,hm⟩
        · exact ⟨0,by intro bad; exact False.elim (hs bad)⟩
      obtain ⟨Lone,hLone⟩ := hOneBound
      obtain ⟨Ltwo,hLtwo⟩ := hTwoBound
      let L := max (k+1) (max K (max Lone Ltwo))
      refine ⟨L,by dsimp [L]; omega,⟨?_,?_⟩⟩
      · intro s hs hRole
        by_cases hOld : s < k
        · obtain ⟨a,b,ha,hb,hla,hlb,hsa,hsb,hMeet⟩ :=
            Q.one s hOld hRole
          exact ⟨a,b,by dsimp [L]; omega,
            by dsimp [L]; omega,hla,hlb,hsa,hsb,hMeet⟩
        · have hsk : s = k := by omega
          subst s
          obtain ⟨a,b,ha,hb,hla,hlb,hsa,hsb,hMeet⟩ :=
            hLone hRole
          exact ⟨a,b,by dsimp [L]; omega,
            by dsimp [L]; omega,hla,hlb,hsa,hsb,hMeet⟩
      · intro s hs hRole
        by_cases hOld : s < k
        · obtain ⟨a,b,c,d,hab,hcd,ha,hb,hc,hd,
            hla,hlb,hlc,hld,hsa,hsc,hMeet⟩ :=
              Q.two s hOld hRole
          exact ⟨a,b,c,d,hab,hcd,
            by dsimp [L]; omega,by dsimp [L]; omega,
            by dsimp [L]; omega,by dsimp [L]; omega,
            hla,hlb,hlc,hld,hsa,hsc,hMeet⟩
        · have hsk : s = k := by omega
          subst s
          obtain ⟨a,b,c,d,hab,hcd,ha,hb,hc,hd,
            hla,hlb,hlc,hld,hsa,hsc,hMeet⟩ :=
              hLtwo hRole
          exact ⟨a,b,c,d,hab,hcd,
            by dsimp [L]; omega,by dsimp [L]; omega,
            by dsimp [L]; omega,by dsimp [L]; omega,
            hla,hlb,hlc,hld,hsa,hsc,hMeet⟩

/-- In the actual simultaneous canonical-flip construction,
all images of source vertices, across ALL canonical source flips,
are bounded by a single explicit cut: the old image of the
finite causal carrier size N. We can enlarge this cut ONCE to
contain actual 1-/2-split witnesses for every split below it.
This is a genuine finite window, not yet a finite diary. -/
theorem exists_canonicalSourceOrbit_finiteWitnessWindow
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n) :
    ∃ bits : Nat → Bool, ∃ k K : Nat,
      RoleDiary
        (onePassRawTarget (canonicalCausalCountableCarrier DA bits)) ∧
      (∀ (i : FiniteCanonicalFlipIndex A n) (z : Nat),
        z < n → canonicalCausalCountableSourceMap DA bits i z < k) ∧
      k ≤ K ∧
      FinitePrefixSplitWitnesses
        (onePassRawTarget (canonicalCausalCountableCarrier DA bits))
        k K := by
  obtain ⟨bits,hDiary,_hEmb⟩ :=
    exists_countableDiary_simultaneousCanonicalSourceFlips_fullEmbedding DA
  let T := canonicalCausalCountableCarrier DA bits
  let N := Fintype.card (FiniteCanonicalSignRootedVertex DA)
  let k := onePassOldImage T N
  have hAll : ∀ (i : FiniteCanonicalFlipIndex A n) (z : Nat),
      z < n → canonicalCausalCountableSourceMap DA bits i z < k := by
    intro i z hz
    have hRank := finiteCanonicalSourceRankMap_lt_carrier DA i z hz
    exact (onePassOldImage_strictMono T) hRank
  obtain ⟨K,hK,hWindow⟩ :=
    exists_finitePrefixSplitWitness_window
      hDiary.toPrediary k
  exact ⟨bits,k,K,hDiary,hAll,hK,hWindow⟩

end DiaryLeafPriority
end ThreeUniformDiaries
