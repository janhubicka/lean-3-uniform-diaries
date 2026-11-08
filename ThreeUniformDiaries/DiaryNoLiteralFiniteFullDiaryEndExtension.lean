import ThreeUniformDiaries.DiaryLiteralOldPrefixTypeMeetTransport
import ThreeUniformDiaries.DiaryFiniteEOneSplitLex
import ThreeUniformDiaries.DiaryFiniteLeafThreeRigidity

/-!
# Track B: a genuine bounded FULL finite diary has no proper literal end-extension

All assertions use FiniteRoleDiaryBlock on its ACTUAL [0,n) frame.
We never treat the zero-extended finite ternary edge table as a
global countable RoleDiary.

The proof is a bounded, positive/negative one-split witness argument.
A candidate new leaf x first splits from each old leaf at an OLD
one-split. At the maximal such meet s, the old full diary already
has a pair of old witnesses for s. V1 positive-class coherence and
the exact new edge bit at s force x to have a strictly larger
singleton meet with at least one old witness, contradiction.

No full ordered-pair meet preservation, "initial segment is diary"
assumption, or unrestricted countable flip absorption is claimed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- At a genuine finite one-split, the sole new singleton type
coordinate at successor cut s+1 is edge(0,s,-), by E1--E5. -/
theorem finite_oneSplit_nextCut_iff
    {G : Ordered3Graph Nat} {m : Nat}
    (P : FiniteRolePrediaryBlock G m)
    (s u v : Nat) (hs : IsOneSplit G s) :
    G.SameOneTypeBelow (s+1) u v ↔
      G.SameOneTypeBelow s u v ∧
      (G.edge 0 s u ↔ G.edge 0 s v) := by
  rw [G.sameOneTypeBelow_succ_iff s u v]
  constructor
  · rintro ⟨hBelow,hBits⟩
    have h0 : 0 < s := by have := hs.1; omega
    exact ⟨hBelow,hBits 0 h0⟩
  · rintro ⟨hBelow,hZero⟩
    refine ⟨hBelow,?_⟩
    intro z hz
    by_cases hIsZero : z = 0
    · subst z
      exact hZero
    · have hzPos : 0 < z := by omega
      exact iff_of_false
        (E_oneSplit_no_positive_aux P.permitted_edge s z u hs hzPos)
        (E_oneSplit_no_positive_aux P.permitted_edge s z v hs hzPos)

/-- A prescribed noncapped singleton meet at an actual one-split
forces opposite zero-marker bits. No ordering of u and v is needed. -/
theorem finite_oneSplit_meet_opposite_bit
    {G : Ordered3Graph Nat} {m : Nat}
    (P : FiniteRolePrediaryBlock G m)
    (s u v : Nat) (hs : IsOneSplit G s)
    (hsu : s < u) (hsv : s < v)
    (hMeet : G.oneMeetLevel u v = s) :
    ¬ (G.edge 0 s u ↔ G.edge 0 s v) := by
  classical
  have hAgree : G.SameOneTypeBelow s u v := by
    rw [← hMeet]
    exact G.oneMeetLevel_agree u v
  have hNoNext : ¬ G.SameOneTypeBelow (s+1) u v := by
    intro hNext
    have hCap : s+1 ≤ min u v := by omega
    have hGreater : s+1 ≤ G.oneMeetLevel u v :=
      Nat.le_findGreatest hCap hNext
    omega
  intro hBit
  exact hNoNext ((finite_oneSplit_nextCut_iff P s u v hs).2
    ⟨hAgree,hBit⟩)

/-- When a/x and p/q split at the same one-split s, the old
witness pair p,q forces one of p,x or q,x to split STRICTLY
later than s. We state the negation of both alternatives,
which is the form needed in a finite maximal-meet argument. -/
theorem finite_no_maximal_meet_at_old_oneSplit
    {G : Ordered3Graph Nat} {m : Nat}
    (P : FiniteRolePrediaryBlock G m)
    (a x p q s : Nat)
    (ha : IsLeaf G a) (hx : IsLeaf G x)
    (hp : IsLeaf G p) (hq : IsLeaf G q)
    (hsa : s < a) (hsx : s < x)
    (hsp : s < p) (hsq : s < q)
    (hs : IsOneSplit G s)
    (hAX : G.oneMeetLevel a x = s)
    (hPQ : G.oneMeetLevel p q = s)
    (hMaxP : G.oneMeetLevel p x ≤ s)
    (hMaxQ : G.oneMeetLevel q x ≤ s) : False := by
  classical
  have hOppAX : ¬ (G.edge 0 s a ↔ G.edge 0 s x) :=
    finite_oneSplit_meet_opposite_bit P s a x hs hsa hsx hAX
  have hOppPQ : ¬ (G.edge 0 s p ↔ G.edge 0 s q) :=
    finite_oneSplit_meet_opposite_bit P s p q hs hsp hsq hPQ
  have hSameAX : G.SameOneTypeBelow s a x := by
    rw [← hAX]
    exact G.oneMeetLevel_agree a x
  have hSamePQ : G.SameOneTypeBelow s p q := by
    rw [← hPQ]
    exact G.oneMeetLevel_agree p q
  have hPair :
      ∃ u v : Nat,
        IsLeaf G u ∧ IsLeaf G v ∧
        s < u ∧ s < v ∧
        G.edge 0 s u ∧ ¬ G.edge 0 s v ∧
        G.SameOneTypeBelow s u v ∧
        G.oneMeetLevel u x ≤ s ∧
        G.oneMeetLevel v x ≤ s := by
    by_cases hpPos : G.edge 0 s p
    · have hqNeg : ¬ G.edge 0 s q := by
        intro hqPos
        exact hOppPQ ⟨fun _ => hqPos, fun _ => hpPos⟩
      exact ⟨p,q,hp,hq,hsp,hsq,hpPos,hqNeg,
        hSamePQ,hMaxP,hMaxQ⟩
    · have hqPos : G.edge 0 s q := by
        by_contra hqNeg
        apply hOppPQ
        exact ⟨fun hp' => False.elim (hpPos hp'),
          fun hq' => False.elim (hqNeg hq')⟩
      have hSameQP : G.SameOneTypeBelow s q p := by
        intro i j hij hj
        exact (hSamePQ hij hj).symm
      exact ⟨q,p,hq,hp,hsq,hsp,hqPos,hpPos,
        hSameQP,hMaxQ,hMaxP⟩
  obtain ⟨u,v,hu,hv,hsu,hsv,huPos,hvNeg,hSameUV,
    hMaxU,hMaxV⟩ := hPair
  by_cases hxPos : G.edge 0 s x
  · have hPositive : G.SameOneTypeBelow s u x :=
      P.one_split_coherent s u x hs hu hx huPos hxPos
    have hSucc : G.SameOneTypeBelow (s+1) u x :=
      (finite_oneSplit_nextCut_iff P s u x hs).2
        ⟨hPositive,⟨fun _ => hxPos,fun _ => huPos⟩⟩
    have hBig : s+1 ≤ G.oneMeetLevel u x :=
      Nat.le_findGreatest (by omega : s+1 ≤ min u x) hSucc
    omega
  · have haPos : G.edge 0 s a := by
      by_contra haNeg
      apply hOppAX
      exact ⟨fun h => False.elim (haNeg h),
        fun h => False.elim (hxPos h)⟩
    have hSameAU : G.SameOneTypeBelow s a u :=
      P.one_split_coherent s a u hs ha hu haPos huPos
    have hSameVX : G.SameOneTypeBelow s v x := by
      intro i j hij hj
      calc
        G.edge i j v ↔ G.edge i j u := (hSameUV hij hj).symm
        _ ↔ G.edge i j a := (hSameAU hij hj).symm
        _ ↔ G.edge i j x := hSameAX hij hj
    have hSucc : G.SameOneTypeBelow (s+1) v x :=
      (finite_oneSplit_nextCut_iff P s v x hs).2
        ⟨hSameVX,iff_of_false hvNeg hxPos⟩
    have hBig : s+1 ≤ G.oneMeetLevel v x :=
      Nat.le_findGreatest (by omega : s+1 ≤ min v x) hSucc
    omega

/-- The last vertex of a nontrivial bounded full diary must be a
leaf: a final one- or two-split would lack bounded later witnesses. -/
theorem FiniteRoleDiaryBlock.last_is_leaf
    {A : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n) (hn : 4 ≤ n) :
    IsLeaf A (n-1) := by
  have h3 : 3 ≤ n-1 := by omega
  have hlt : n-1 < n := by omega
  rcases DA.prediary.role_valid (n-1) h3 hlt with hLeaf | hOne | hTwo
  · exact hLeaf
  · obtain ⟨a,b,ha,_,_,_,hsa,_,_⟩ :=
      DA.prediary.one_split_witness (n-1) hOne hlt
    omega
  · obtain ⟨a,b,c,d,_,_,ha,_,_,_,_,_,_,_,hsa,_,_⟩ :=
      DA.prediary.two_split_witness (n-1) hTwo hlt
    omega

/-- An induced old FULL finite diary prefix cannot acquire a NEW
leaf in any larger genuine full finite target. The real finite
old witnesses at each split enforce an impossible maximal meet.

The literal prefix hypothesis is the exact all-edge/nonedge
third-coordinate restriction, already handled by the separate
old-type/meet/role transfer module. -/
theorem no_new_leaf_of_literal_full_diary_prefix
    {A C : Ordered3Graph Nat} {n m : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (DC : FiniteRoleDiaryBlock C m)
    (hn : 4 ≤ n)
    (hPrefix : LiteralOldPrefixAgreement A C n)
    (x : Nat) (hnx : n ≤ x) (hxm : x < m)
    (hx : IsLeaf C x) : False := by
  classical
  let L : Finset Nat := (Finset.range n).filter (IsLeaf A)
  have hLmem (u : Nat) : u ∈ L ↔ u < n ∧ IsLeaf A u := by
    simp [L]
  have hLnonempty : L.Nonempty := by
    refine ⟨n-1,(hLmem (n-1)).2 ⟨by omega,?_⟩⟩
    exact DA.last_is_leaf hn
  let S : Finset Nat := L.image (fun u => C.oneMeetLevel u x)
  have hSnonempty : S.Nonempty := hLnonempty.image _
  let s : Nat := S.max' hSnonempty
  have hsMem : s ∈ S := Finset.max'_mem S hSnonempty
  obtain ⟨a,haL,hMeet⟩ := Finset.mem_image.mp hsMem
  have han : a < n := ((hLmem a).mp haL).1
  have hLeafA : IsLeaf A a := ((hLmem a).mp haL).2
  have hLeafCA : IsLeaf C a :=
    ((role_iff_of_literalOldPrefix hPrefix a han).1).mp hLeafA
  have hax : a < x := by omega
  have hMax (u : Nat) (hun : u < n) (hu : IsLeaf A u) :
      C.oneMeetLevel u x ≤ s := by
    have huL : u ∈ L := (hLmem u).2 ⟨hun,hu⟩
    have huS : C.oneMeetLevel u x ∈ S :=
      Finset.mem_image.mpr ⟨u,huL,rfl⟩
    exact Finset.le_max' S _ huS
  have hsC : IsOneSplit C s := by
    have hOne : IsOneSplit C (C.oneMeetLevel a x) :=
      DC.singleton_meets a x hax hxm hLeafCA hx
    simpa only [hMeet] using hOne
  have hsn : s < n := by
    have hc := C.oneMeetLevel_le_min a x
    rw [hMeet] at hc
    omega
  have hsA : IsOneSplit A s :=
    ((role_iff_of_literalOldPrefix hPrefix s hsn).2.1).mpr hsC
  obtain ⟨p,q,hpn,hqn,hLeafP,hLeafQ,hsp,hsq,hOldPQ⟩ :=
    DA.prediary.one_split_witness s hsA hsn
  have hLeafCP : IsLeaf C p :=
    ((role_iff_of_literalOldPrefix hPrefix p hpn).1).mp hLeafP
  have hLeafCQ : IsLeaf C q :=
    ((role_iff_of_literalOldPrefix hPrefix q hqn).1).mp hLeafQ
  have hPQ : C.oneMeetLevel p q = s := by
    rw [← (oneMeetLevel_eq_of_literalOldPrefix hPrefix p q hpn hqn)]
    exact hOldPQ
  have hsa : s < a := by
    have hcap := C.oneMeetLevel_le_min a x
    rw [hMeet] at hcap
    have hNE : s ≠ a := by
      intro heq
      have hOneA : IsOneSplit C a := by
        simpa only [heq] using hsC
      exact hLeafCA.2.1 hOneA.2.1
    omega
  have hsx : s < x := by omega
  exact finite_no_maximal_meet_at_old_oneSplit
    DC.prediary a x p q s
    hLeafCA hx hLeafCP hLeafCQ
    hsa hsx hsp hsq hsC hMeet hPQ
    (hMax p hpn hLeafP) (hMax q hqn hLeafQ)

/-- Main obstruction: no proper LITERAL end extension of any
nontrivial finite full diary, even if the bigger target is otherwise
allowed arbitrary additional edges and vertices after the old bound.

Moving protected embeddings are not ruled out. -/
theorem no_proper_literal_full_diary_end_extension
    {A C : Ordered3Graph Nat} {n m : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (DC : FiniteRoleDiaryBlock C m)
    (hn : 4 ≤ n)
    (hnm : n ≤ m)
    (hPrefix : LiteralOldPrefixAgreement A C n) :
    m = n := by
  by_contra hne
  have hnmStrict : n < m := by omega
  rcases DC.prediary.role_valid n (by omega) hnmStrict with
      hLeaf | hOne | hTwo
  · exact no_new_leaf_of_literal_full_diary_prefix
      DA DC hn hPrefix n (le_refl n) hnmStrict hLeaf
  · obtain ⟨a,b,han,_,ha,_,hna,_,_⟩ :=
      DC.prediary.one_split_witness n hOne hnmStrict
    exact no_new_leaf_of_literal_full_diary_prefix
      DA DC hn hPrefix a (by omega) han ha
  · obtain ⟨a,b,c,d,_,_,han,_,_,_,ha,_,_,_,hna,_,_⟩ :=
      DC.prediary.two_split_witness n hTwo hnmStrict
    exact no_new_leaf_of_literal_full_diary_prefix
      DA DC hn hPrefix a (by omega) han ha


/-- The ordinary finite induced-prefix hypothesis only mentions
INCREASING old triples. E1--E5 ordered-edge support makes this
equivalent to full literal agreement on all old third-coordinate
tests; the zero-extended tails play no role. -/
theorem literalOldPrefixAgreement_of_induced_finite
    {A C : Ordered3Graph Nat} {n m : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (DC : FiniteRoleDiaryBlock C m)
    (hInd : ∀ a b c : Nat, a < b → b < c → c < n →
      (A.edge a b c ↔ C.edge a b c)) :
    LiteralOldPrefixAgreement A C n := by
  intro a b c hc
  by_cases hOrder : a < b ∧ b < c
  · exact hInd a b c hOrder.1 hOrder.2 hc
  · have hA : ¬ A.edge a b c := by
      intro he
      have h := DA.prediary.frame.edge_support a b c he
      exact hOrder ⟨h.1,h.2.1⟩
    have hC : ¬ C.edge a b c := by
      intro he
      have h := DC.prediary.frame.edge_support a b c he
      exact hOrder ⟨h.1,h.2.1⟩
    exact iff_of_false hA hC

/-- User-facing sharp finite formulation: induction of ALL edges
and nonedges on the old ordered initial segment suffices to rule
out any proper finite FULL diary end extension. -/
theorem no_proper_full_diary_end_extension_of_induced_prefix
    {A C : Ordered3Graph Nat} {n m : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (DC : FiniteRoleDiaryBlock C m)
    (hn : 4 ≤ n) (hnm : n ≤ m)
    (hInd : ∀ a b c : Nat, a < b → b < c → c < n →
      (A.edge a b c ↔ C.edge a b c)) :
    m = n := by
  exact no_proper_literal_full_diary_end_extension
    DA DC hn hnm
    (literalOldPrefixAgreement_of_induced_finite DA DC hInd)

end DiaryLeafPriority
end ThreeUniformDiaries
