import ThreeUniformDiaries.DiaryFiniteLeafMeetMarkerReindex

/-!
# Forward transport of singleton and full two-types under compression

The induced increasing finite support may omit infinitely many old
test coordinates. It therefore CANNOT preserve arbitrary numerical
meets automatically: missing tests can delay first disagreement.
The safe general statement is one-directional.

If two old singleton codes agree through an old selected cut,
then their reindexed codes agree through the corresponding new cut.
Likewise for full ordered-pair types, provided the selected cut
does not exceed the relevant first coordinate caps. The proof
uses only increasing enumeration, surjective induced edge copying
and the fact that a compressed earlier test is an actual old
earlier test.

These lemmas are the lower-bound half of first-disagreement
preservation for selected leaf meets. The reverse bound must be
proved separately using an explicit retained distinguishing edge
at the selected meet (one-split zero-marker or two-split auxiliary).
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {G : Ordered3Graph Nat} {S : Finset Nat}

/-- Every old singleton-type agreement at a selected cut survives
in the induced finite restriction. No claim of the converse is
made: omitted old coordinates may distinguish the old vertices. -/
theorem finiteSupportGraph_oneType_of_original
    (l u v : Nat)
    (hl : l < S.card) (hu : u < S.card) (hv : v < S.card)
    (hlu : l ≤ u) (hlv : l ≤ v)
    (hSource :
      G.SameOneTypeBelow (finiteSupportIndex S l)
        (finiteSupportIndex S u) (finiteSupportIndex S v)) :
    (finiteSupportGraph G S).SameOneTypeBelow l u v := by
  intro a b hab hbl
  have hbu : b < u := by omega
  have hbv : b < v := by omega
  have hbCard : b < S.card := by omega
  have haCard : a < S.card := by omega
  have hOldAB := finiteSupportIndex_strictMono
    S a b hab hbCard
  have hOldBL := finiteSupportIndex_strictMono
    S b l hbl hl
  calc
    (finiteSupportGraph G S).edge a b u ↔
      G.edge (finiteSupportIndex S a) (finiteSupportIndex S b)
        (finiteSupportIndex S u) :=
        finiteSupportGraph_edge_iff G S a b u hab hbu hu
    _ ↔ G.edge (finiteSupportIndex S a) (finiteSupportIndex S b)
        (finiteSupportIndex S v) :=
        hSource hOldAB hOldBL
    _ ↔ (finiteSupportGraph G S).edge a b v :=
        (finiteSupportGraph_edge_iff G S a b v hab hbv hv).symm

/-- Every full ordered-pair type agreement through a selected
old cut is inherited by the compressed finite restriction.
Both singleton coordinates and auxiliary pair coordinates
are checked explicitly, at the same selected cut. -/
theorem finiteSupportGraph_twoType_of_original
    (l a b c d : Nat)
    (hl : l < S.card)
    (ha : a < S.card) (hb : b < S.card)
    (hc : c < S.card) (hd : d < S.card)
    (hab : a < b) (hcd : c < d)
    (hla : l ≤ a) (hlc : l ≤ c)
    (hSource :
      G.SameTwoTypeBelow (finiteSupportIndex S l)
        (finiteSupportIndex S a) (finiteSupportIndex S b)
        (finiteSupportIndex S c) (finiteSupportIndex S d)) :
    (finiteSupportGraph G S).SameTwoTypeBelow l a b c d := by
  refine ⟨?_, ?_, ?_⟩
  · exact finiteSupportGraph_oneType_of_original
      (G := G) (S := S)
      l a c hl ha hc hla hlc hSource.1
  · exact finiteSupportGraph_oneType_of_original
      (G := G) (S := S)
      l b d hl hb hd (by omega) (by omega) hSource.2.1
  · intro x hx
    have hxa : x < a := by omega
    have hxc : x < c := by omega
    have hxCard : x < S.card := by omega
    have hOldXL := finiteSupportIndex_strictMono
      S x l hx hl
    calc
      (finiteSupportGraph G S).edge x a b ↔
        G.edge (finiteSupportIndex S x)
          (finiteSupportIndex S a) (finiteSupportIndex S b) :=
        finiteSupportGraph_edge_iff G S x a b hxa hab hb
      _ ↔ G.edge (finiteSupportIndex S x)
          (finiteSupportIndex S c) (finiteSupportIndex S d) :=
        hSource.2.2 hOldXL
      _ ↔ (finiteSupportGraph G S).edge x c d :=
        (finiteSupportGraph_edge_iff G S x c d hxc hcd hd).symm

end DiaryLeafPriority
end ThreeUniformDiaries
