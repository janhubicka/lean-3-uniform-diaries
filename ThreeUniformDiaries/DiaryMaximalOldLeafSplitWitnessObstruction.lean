import ThreeUniformDiaries.DiaryOneSplitWitnessClasses
import ThreeUniformDiaries.DiaryFiniteEOneSplitLex

/-!
# Track B: a maximal old-leaf singleton meet cannot occur at a
# one-split with a complete old positive/negative witness pair

This is the local combinatorial step of the adversarial English
no-literal-full-diary-end-extension lemma. It uses the ACTUAL
countable RoleDiary V1/S1 interfaces, and is deliberately
formulated with four genuine leaves a,x,p,q and a split s.
The old witness pair p,q must already split at s.

If s is the meet of a with a new leaf x, while p and q are old
witness leaves splitting at the same s, then one of p or q has
meet with x STRICTLY GREATER than s. The positive/negative
witness bits and V1 force this; no independent Boolean
assignment or external extension premise is introduced.

An application to bounded FINITE diary prefixes must separately
verify transfer of the old source witnesses and their meets
into the target. We do NOT pretend a zero-extended finite
diary is a global RoleDiary on Nat.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority
namespace RoleDiary

/-- Key local maximal-meet contradiction. The target is a genuine
RoleDiary on Nat. We only assume the two old witnesses p,q have
a first singleton split s, while a and x also meet at s.
If p and q have no larger meet with x, V1 positive-class
coherence yields a contradiction.

No claim about arbitrary finite-frame source prefixes is smuggled
in: the finite-prefix transfer is a separate interface. -/
theorem no_maximal_oneMeet_at_witnessed_oneSplit
    {H : Ordered3Graph Nat} (D : RoleDiary H)
    (a x p q s : Nat)
    (ha : IsLeaf H a) (hx : IsLeaf H x)
    (hp : IsLeaf H p) (hq : IsLeaf H q)
    (hax : a < x)
    (hs : IsOneSplit H s)
    (hMeetAX : H.oneMeetLevel a x = s)
    (hMeetPQ : H.oneMeetLevel p q = s)
    (hBoundP : H.oneMeetLevel p x ≤ s)
    (hBoundQ : H.oneMeetLevel q x ≤ s) : False := by
  classical
  have hsa : s < a := by
    have hCap := H.oneMeetLevel_le_min a x
    rw [hMeetAX] at hCap
    have hnot : s ≠ a := by
      intro heq
      have hOneA : IsOneSplit H a := by simpa only [heq] using hs
      exact ha.2.1 hOneA.2.1
    omega
  have hsx : s < x := lt_trans hsa hax
  have hsp : s < p := by
    have hCap := H.oneMeetLevel_le_min p q
    rw [hMeetPQ] at hCap
    have hnot : s ≠ p := by
      intro heq
      have hOneP : IsOneSplit H p := by simpa only [heq] using hs
      exact hp.2.1 hOneP.2.1
    omega
  have hsq : s < q := by
    have hCap := H.oneMeetLevel_le_min p q
    rw [hMeetPQ] at hCap
    have hnot : s ≠ q := by
      intro heq
      have hOneQ : IsOneSplit H q := by simpa only [heq] using hs
      exact hq.2.1 hOneQ.2.1
    omega
  have hOppAX : ¬ (H.edge 0 s a ↔ H.edge 0 s x) :=
    D.oneSplit_witness_opposite_marker
      s a x hs ha hx hsa hsx hMeetAX
  have hOppPQ : ¬ (H.edge 0 s p ↔ H.edge 0 s q) :=
    D.oneSplit_witness_opposite_marker
      s p q hs hp hq hsp hsq hMeetPQ
  have hSameAX : H.SameOneTypeBelow s a x := by
    rw [← hMeetAX]
    exact H.oneMeetLevel_agree a x
  have hSamePQ : H.SameOneTypeBelow s p q := by
    rw [← hMeetPQ]
    exact H.oneMeetLevel_agree p q
  have hPair :
      ∃ u v : Nat,
        IsLeaf H u ∧ IsLeaf H v ∧
        s < u ∧ s < v ∧
        H.edge 0 s u ∧ ¬ H.edge 0 s v ∧
        H.SameOneTypeBelow s u v ∧
        H.oneMeetLevel u x ≤ s ∧
        H.oneMeetLevel v x ≤ s := by
    by_cases hpPos : H.edge 0 s p
    · have hqNeg : ¬ H.edge 0 s q := by
        intro hqPos
        exact hOppPQ ⟨fun _ => hqPos, fun _ => hpPos⟩
      exact ⟨p,q,hp,hq,hsp,hsq,hpPos,hqNeg,
        hSamePQ,hBoundP,hBoundQ⟩
    · have hqPos : H.edge 0 s q := by
        by_contra hqNeg
        apply hOppPQ
        exact ⟨fun hp' => False.elim (hpPos hp'),
          fun hq' => False.elim (hqNeg hq')⟩
      have hSameQP : H.SameOneTypeBelow s q p := by
        intro i j hij hj
        exact (hSamePQ hij hj).symm
      exact ⟨q,p,hq,hp,hsq,hsp,hqPos,hpPos,
        hSameQP,hBoundQ,hBoundP⟩
  obtain ⟨u,v,hu,hv,hsu,hsv,huPos,hvNeg,hSameUV,
    hMaxU,hMaxV⟩ := hPair
  by_cases hxPos : H.edge 0 s x
  · have hPositive : H.SameOneTypeBelow (s+1) u x :=
      D.oneSplit_incident_oneTypes_succ
        s u x hs hu hx huPos hxPos
    have hHigh : s+1 ≤ H.oneMeetLevel u x :=
      Nat.le_findGreatest (by omega : s+1 ≤ min u x) hPositive
    omega
  · have haPos : H.edge 0 s a := by
      by_contra haNeg
      apply hOppAX
      exact ⟨fun he => False.elim (haNeg he),
        fun he => False.elim (hxPos he)⟩
    have hSameAU : H.SameOneTypeBelow s a u :=
      D.one_split_coherent s a u hs ha hu haPos huPos
    have hSameVX : H.SameOneTypeBelow s v x := by
      intro i j hij hj
      calc
        H.edge i j v ↔ H.edge i j u := (hSameUV hij hj).symm
        _ ↔ H.edge i j a := (hSameAU hij hj).symm
        _ ↔ H.edge i j x := hSameAX hij hj
    have hSameBit : H.edge 0 s v ↔ H.edge 0 s x :=
      iff_of_false hvNeg hxPos
    have hNegative : H.SameOneTypeBelow (s+1) v x :=
      (D.sameOneTypeBelow_succ_iff_of_oneSplit
        s v x hs hv hx).2 ⟨hSameVX,hSameBit⟩
    have hHigh : s+1 ≤ H.oneMeetLevel v x :=
      Nat.le_findGreatest (by omega : s+1 ≤ min v x) hNegative
    omega


/-- A genuinely countable full diary cannot acquire a new leaf beyond a
finite cut when the old cut already contains at least one leaf and
contains complete old witness pairs for EVERY old one-split.

This is a FINITE-CHOICE consequence of the maximal-meet lemma.
It does not assume a zero-extended finite diary is a RoleDiary. -/
theorem no_later_leaf_of_bounded_old_split_witnesses
    {H : Ordered3Graph Nat} (D : RoleDiary H)
    (n x : Nat) (hn : 3 ≤ n) (hnx : n ≤ x)
    (hx : IsLeaf H x)
    (hOld : ∃ a : Nat, a < n ∧ IsLeaf H a)
    (hWitness :
      ∀ s : Nat, s < n → IsOneSplit H s →
        ∃ p q : Nat, p < n ∧ q < n ∧
          IsLeaf H p ∧ IsLeaf H q ∧
          H.oneMeetLevel p q = s) : False := by
  classical
  let L : Finset Nat := (Finset.range n).filter (IsLeaf H)
  have hLmem (u : Nat) :
      u ∈ L ↔ u < n ∧ IsLeaf H u := by
    simp [L]
  have hLnonempty : L.Nonempty := by
    obtain ⟨a,ha,hLeafA⟩ := hOld
    exact ⟨a,(hLmem a).2 ⟨ha,hLeafA⟩⟩
  let S : Finset Nat := L.image (fun u => H.oneMeetLevel u x)
  have hSnonempty : S.Nonempty := hLnonempty.image _
  let s : Nat := S.max' hSnonempty
  have hsMem : s ∈ S := Finset.max'_mem S hSnonempty
  obtain ⟨a,haL,hMeet⟩ := Finset.mem_image.mp hsMem
  have han : a < n := ((hLmem a).mp haL).1
  have hLeafA : IsLeaf H a := ((hLmem a).mp haL).2
  have hax : a < x := by omega
  have hMax (u : Nat) (hu : u < n)
      (hLeafU : IsLeaf H u) :
      H.oneMeetLevel u x ≤ s := by
    have huL : u ∈ L := (hLmem u).2 ⟨hu,hLeafU⟩
    have huS : H.oneMeetLevel u x ∈ S :=
      Finset.mem_image.mpr ⟨u,huL,rfl⟩
    exact Finset.le_max' S _ huS
  have hsSplit : IsOneSplit H s := by
    have hOne : IsOneSplit H (H.oneMeetLevel a x) :=
      D.singleton_meets a x hLeafA hx (by omega)
    simpa only [hMeet] using hOne
  have hsn : s < n := by
    have hCap := H.oneMeetLevel_le_min a x
    rw [hMeet] at hCap
    omega
  obtain ⟨p,q,hpn,hqn,hLeafP,hLeafQ,hPQ⟩ :=
    hWitness s hsn hsSplit
  exact D.no_maximal_oneMeet_at_witnessed_oneSplit
    a x p q s hLeafA hx hLeafP hLeafQ hax
    hsSplit hMeet hPQ
    (hMax p hpn hLeafP) (hMax q hqn hLeafQ)

/-- In a countable full RoleDiary there cannot be a finite cut
containing an old leaf and all genuine bounded witnesses for all
one-splits below that cut. Any vertex at/after the cut either
is a leaf or has future witness leaves, and both options conflict
with the preceding maximal-meet argument.

This isolates exactly the saturation obstruction faced by literal
finite FULL diary prefixes, without asserting the missing transfer
lemma from the separate finite RoleDiaryBlock encoding. -/
theorem no_finite_saturated_oneSplit_prefix
    {H : Ordered3Graph Nat} (D : RoleDiary H)
    (n : Nat) (hn : 3 ≤ n)
    (hOld : ∃ a : Nat, a < n ∧ IsLeaf H a)
    (hWitness :
      ∀ s : Nat, s < n → IsOneSplit H s →
        ∃ p q : Nat, p < n ∧ q < n ∧
          IsLeaf H p ∧ IsLeaf H q ∧
          H.oneMeetLevel p q = s) : False := by
  rcases D.role_valid n hn with hLeaf | hOne | hTwo
  · exact D.no_later_leaf_of_bounded_old_split_witnesses
      n n hn (le_refl n) hLeaf hOld hWitness
  · obtain ⟨a,b,ha,hb,hna,hnb,hMeet⟩ :=
      D.one_split_witness n hOne
    exact D.no_later_leaf_of_bounded_old_split_witnesses
      n a hn (by omega) ha hOld hWitness
  · obtain ⟨a,b,c,d,hab,hcd,ha,hb,hc,hd,hna,hnc,hMeet⟩ :=
      D.two_split_witness n hTwo
    exact D.no_later_leaf_of_bounded_old_split_witnesses
      n a hn (by omega) ha hOld hWitness


end RoleDiary
end DiaryLeafPriority
end ThreeUniformDiaries
