import ThreeUniformDiaries.DiaryFiniteUniversalBound

/-!
# The first finite diary flip property, in the paper's language

A finite flip is an identity diary-pre-embedding: the source and
target are both complete finite diaries on the same ordered
initial segment, with identical roles, leaf-induced ternary
relations and capped singleton/full ordered-pair meets of
genuine leaves.

The E/V/S and mixed tuples involving split vertices may differ.
This is NOT an ordinary FiniteMeetEmbedding under identity.

The previously verified finite bounded-universality theorem now
proves the FIRST statement of the paper's flip proposition in
this faithful finite representation, in fact in a stronger form:
one finite diary contains ALL finite diaries of the source bound,
not only all flips of the given source.

The SECOND statement, absorption of the source in EVERY flip
of the target, does NOT follow. Its geometric causality and
root-profile consistency remain unproved.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Finite flips, exactly identity-on-vertices diary
pre-embeddings between two genuine finite diaries. Only
LEAF meets are preserved, not arbitrary mixed split tuples. -/
structure FiniteDiaryFlip
    (A B : Ordered3Graph Nat) (n : Nat) : Prop where
  source_diary : FiniteRoleDiaryBlock A n
  target_diary : FiniteRoleDiaryBlock B n
  role_iff :
    ∀ u : Nat, 3 ≤ u → u < n →
      (IsLeaf A u ↔ IsLeaf B u) ∧
      (IsOneSplit A u ↔ IsOneSplit B u) ∧
      (IsTwoSplit A u ↔ IsTwoSplit B u)
  leaf_edge_iff :
    ∀ a b c : Nat, a < b → b < c → c < n →
      IsLeaf A a → IsLeaf A b → IsLeaf A c →
      (A.edge a b c ↔ B.edge a b c)
  leaf_oneMeet :
    ∀ a b : Nat, a < n → b < n →
      IsLeaf A a → IsLeaf A b →
      A.oneMeetLevel a b = B.oneMeetLevel a b
  leaf_twoMeet :
    ∀ a b c d : Nat, a < b → c < d →
      b < n → d < n →
      IsLeaf A a → IsLeaf A b →
      IsLeaf A c → IsLeaf A d →
      A.twoMeetLevel a b c d = B.twoMeetLevel a b c d

/-- Identity is a flip: reflexivity of the literal finite
pre-embedding data. -/
theorem FiniteDiaryFlip.refl
    {A : Ordered3Graph Nat} {n : Nat}
    (D : FiniteRoleDiaryBlock A n) :
    FiniteDiaryFlip A A n := by
  refine {
    source_diary := D
    target_diary := D
    role_iff := ?_
    leaf_edge_iff := ?_
    leaf_oneMeet := ?_
    leaf_twoMeet := ?_
  }
  · intro u hu3 hun
    exact ⟨Iff.rfl,Iff.rfl,Iff.rfl⟩
  · intro a b c hab hbc hc ha hb hcLeaf
    exact Iff.rfl
  · intro a b ha hb hLa hLb
    rfl
  · intro a b c d hab hcd hb hd hLa hLb hLc hLd
    rfl

/-- The flip relation is symmetric: preserving leaf relations
and their exact numerical meet levels is a two-way condition. -/
theorem FiniteDiaryFlip.symm
    {A B : Ordered3Graph Nat} {n : Nat}
    (F : FiniteDiaryFlip A B n) :
    FiniteDiaryFlip B A n := by
  refine {
    source_diary := F.target_diary
    target_diary := F.source_diary
    role_iff := ?_
    leaf_edge_iff := ?_
    leaf_oneMeet := ?_
    leaf_twoMeet := ?_
  }
  · intro u hu3 hun
    obtain ⟨hl,ho,ht⟩ := F.role_iff u hu3 hun
    exact ⟨hl.symm,ho.symm,ht.symm⟩
  · intro a b c hab hbc hc ha hb hcLeaf
    have hLa : IsLeaf A a :=
      ((F.role_iff a ha.1 (by omega)).1).mpr ha
    have hLb : IsLeaf A b :=
      ((F.role_iff b hb.1 (by omega)).1).mpr hb
    have hLc : IsLeaf A c :=
      ((F.role_iff c hcLeaf.1 hc).1).mpr hcLeaf
    exact (F.leaf_edge_iff a b c hab hbc hc hLa hLb hLc).symm
  · intro a b ha hb hLa hLb
    have hA : IsLeaf A a :=
      ((F.role_iff a hLa.1 ha).1).mpr hLa
    have hB : IsLeaf A b :=
      ((F.role_iff b hLb.1 hb).1).mpr hLb
    exact (F.leaf_oneMeet a b ha hb hA hB).symm
  · intro a b c d hab hcd hb hd hLa hLb hLc hLd
    have hA : IsLeaf A a :=
      ((F.role_iff a hLa.1 (by omega)).1).mpr hLa
    have hB : IsLeaf A b :=
      ((F.role_iff b hLb.1 hb).1).mpr hLb
    have hC : IsLeaf A c :=
      ((F.role_iff c hLc.1 (by omega)).1).mpr hLc
    have hD : IsLeaf A d :=
      ((F.role_iff d hLd.1 hd).1).mpr hLd
    exact (F.leaf_twoMeet a b c d hab hcd hb hd
      hA hB hC hD).symm

/-- FIRST half of the manuscript flip property, in the
faithful bounded finite-language representation.

For every finite source diary A there exists one finite diary
B admitting an induced, exact ALL-MIXED-MEET preserving diary
embedding of each flip A' of A. A' has the same n vertices.

There is no assertion about embeddings A -> B' for EVERY
flip B' of B; that is the genuine remaining mathematical gap. -/
theorem exists_finiteDiary_for_all_source_flips
    (A : Ordered3Graph Nat) (n : Nat)
    (DA : FiniteRoleDiaryBlock A n) :
    ∃ (B : Ordered3Graph Nat) (k : Nat),
      FiniteRoleDiaryBlock B k ∧
      ∀ A' : Ordered3Graph Nat,
        FiniteDiaryFlip A A' n →
          ∃ f : Nat → Nat, FiniteMeetEmbedding A' B n f := by
  obtain ⟨B,k,DB,hUniversal⟩ :=
    exists_finiteDiary_universal_bound n
  refine ⟨B,k,DB,?_⟩
  intro A' hFlip
  exact hUniversal A' hFlip.target_diary

/-- The still-unproved SECOND direction, as a precise finite
predicate. Naming it does not establish it. -/
def AbsorbsEveryTargetFlip
    (A B : Ordered3Graph Nat) (n k : Nat) : Prop :=
  ∀ B' : Ordered3Graph Nat,
    FiniteDiaryFlip B B' k →
      ∃ f : Nat → Nat, FiniteMeetEmbedding A B' n f

end DiaryLeafPriority
end ThreeUniformDiaries
