import ThreeUniformDiaries.DiaryFiniteLeafSupportCoversPrefix
import ThreeUniformDiaries.DiaryNoLiteralFiniteFullDiaryEndExtension

/-!
# Track B: no nontrivial complete finite FULL diary is a literal prefix of a countable diary

The verified finite no-end-extension theorem rules out a full finite
diary [0,n) being an induced literal prefix of a larger finite FULL diary.

We strengthen this to COUNTABLE full RoleDiaries using the verified
cofinal finite leaf-meet support extraction: a hypothetical countable
full target K agreeing with an old full finite A on [0,n) admits a
genuine finite full compression that retains the prefix [0,n+1)
literally. This would give a larger FULL finite diary C with the old
A as its literal initial segment, contradicting the finite theorem.

It is essential that one extra countable target vertex n is included
in the finite leaf-meet support: this guarantees STRICT target frame
growth, rather than merely an equal-size compression.

This negative theorem does not rule out protected proper INITIAL
prefixes (which are not full finite diaries), nor moving exact-meet
embeddings into other countable diaries. The distinction is central to
the still OPEN protected relative finite absorber construction.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- A complete genuine full finite diary of size at least four
cannot be the literal entire old prefix of ANY genuine countable
RoleDiary on Nat, even when only the exact induced edge and
nonedge table on increasing old triples is prescribed. -/
theorem no_literal_full_finite_diary_prefix_in_countable
    {A K : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (DK : RoleDiary K)
    (hn : 4 ≤ n)
    (hPrefix : LiteralOldPrefixAgreement A K n) : False := by
  classical
  obtain ⟨L,hLeaves,DC,hKeep⟩ :=
    DK.exists_finite_full_diary_retaining_prefix (n+1)
  let S : Finset Nat := finiteLeafMeetSupport K L
  let C : Ordered3Graph Nat := finiteSupportGraph K S
  have hStrict : n < S.card := (hKeep n (by omega)).1
  have hInd :
      ∀ a b c : Nat, a < b → b < c → c < n →
        (A.edge a b c ↔ C.edge a b c) := by
    intro a b c hab hbc hcn
    have ha : a < n+1 := by omega
    have hb : b < n+1 := by omega
    have hc : c < n+1 := by omega
    have haFixed : finiteSupportIndex S a = a := (hKeep a ha).2
    have hbFixed : finiteSupportIndex S b = b := (hKeep b hb).2
    have hcFixed : finiteSupportIndex S c = c := (hKeep c hc).2
    have hcBound : c < S.card := (hKeep c hc).1
    have hC : C.edge a b c ↔ K.edge a b c := by
      have h := finiteSupportGraph_edge_iff K S a b c hab hbc hcBound
      simpa only [C,haFixed,hbFixed,hcFixed] using h
    exact (hPrefix a b c hcn).trans hC.symm
  have hSame :
      S.card = n :=
    no_proper_full_diary_end_extension_of_induced_prefix
      DA DC hn (by omega : n ≤ S.card) hInd
  omega

/-- Equivalent user-facing negative statement: genuine
countable-diary extension of a full finite diary cannot preserve
the entire old finite edge/nonedge initial segment, even without
a specified embedding of other vertices or preservation of
mixed numerical meets. -/
theorem no_literal_full_finite_diary_prefix_of_induced
    {A K : Ordered3Graph Nat} {n : Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (DK : RoleDiary K)
    (hn : 4 ≤ n)
    (hInd : ∀ a b c : Nat, a < b → b < c → c < n →
      (A.edge a b c ↔ K.edge a b c)) : False := by
  have hPrefix : LiteralOldPrefixAgreement A K n := by
    intro a b c hc
    by_cases hord : a < b ∧ b < c
    · exact hInd a b c hord.1 hord.2 hc
    · have ha : ¬ A.edge a b c := by
        intro he
        have hs := DA.prediary.frame.edge_support a b c he
        exact hord ⟨hs.1,hs.2.1⟩
      have hk : ¬ K.edge a b c := by
        intro he
        exact hord (DK.edge_ordered a b c he)
      exact iff_of_false ha hk
  exact no_literal_full_finite_diary_prefix_in_countable DA DK hn hPrefix

end DiaryLeafPriority
end ThreeUniformDiaries
