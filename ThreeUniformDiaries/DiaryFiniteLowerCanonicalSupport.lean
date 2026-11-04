import ThreeUniformDiaries.DiaryFiniteExactImageSupport
import ThreeUniformDiaries.DiaryFiniteLeafMeetOrderReindex

/-!
# Track C / lower bridge: exact canonical support of a finite diary embedding

The existing finite lower-bound theorem supplies an ACTUAL numerical
meet-preserving embedding f of a finite full diary H into an arbitrary
countable full diary T with all source leaves in a prescribed range.

The verified exact-support-image theorem (#986) gives set equality:
the target finite leaf-meet support of f's source leaves is exactly
f[the full finite vertex interval]. Since f is strictly increasing,
this equality is stronger than mere set preservation: the canonical
INCREASING enumeration of the target support has the exact old
source-vertex values at every source index.

Here we prove the cardinality, numerical index, and induced
edge/NONEDGE table of that canonical support. Thus a finite
diary source embedded in an arbitrary leaf range is recovered
LITERALLY by reindexing the range's generated leaf support,
rather than only up to an unspecified finite isomorphism.

This is a finite canonical-colouring transport lemma. It does
NOT by itself construct the global colouring of all A-copies
or prove the exact big Ramsey lower bound; that next step has
to transport the chosen marked labels through the fixed
countable diary leaf identification. It uses neither countable
diary unavoidability nor a new Ramsey theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

open Ordered3Graph

/-- An increasing finite map f enumerates its own finite image
in precisely the same order as Mathlib's canonical sorted
Finset enumeration. The source tail of f is irrelevant. -/
theorem finiteSupportIndex_rangeImage_eq
    (n : Nat) (f : Nat → Nat)
    (hf : StrictMono f)
    (i : Nat) (hi : i < n) :
    finiteSupportIndex ((Finset.range n).image f) i = f i := by
  classical
  let S : Finset Nat := (Finset.range n).image f
  have hCard : S.card = n := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ hf.injective]
    simp
  have hMem : ∀ j : Fin n, f j.val ∈ S := by
    intro j
    exact Finset.mem_image.mpr
      ⟨j.val, Finset.mem_range.mpr j.isLt, rfl⟩
  have hMon : StrictMono (fun j : Fin n => f j.val) := by
    intro j k hjk
    exact hf hjk
  have hUnique :
      (fun j : Fin n => f j.val) = S.orderEmbOfFin hCard :=
    Finset.orderEmbOfFin_unique hCard hMem hMon
  have hiS : i < S.card := by omega
  calc
    finiteSupportIndex S i =
        S.orderEmbOfFin rfl ⟨i,hiS⟩ :=
      finiteSupportIndex_of_lt S i hiS
    _ = S.orderEmbOfFin hCard ⟨i,hi⟩ := by
      apply (Finset.orderEmbOfFin_eq_orderEmbOfFin_iff).2
      rfl
    _ = f i := by
      simpa using (congrFun hUnique ⟨i,hi⟩).symm

/-- A full numerical finite diary embedding is recovered
exactly on the canonical target support of its image leaves:
the support has exactly n vertices, and its increasing
reindexing is literally the original f on every vertex. -/
theorem FiniteMeetEmbedding.canonical_leafSupport_card_and_index
    {H T : Ordered3Graph Nat} {n : Nat} {f : Nat → Nat}
    (D : FiniteRoleDiaryBlock H n)
    (E : FiniteMeetEmbedding H T n f)
    (L : Finset Nat)
    (hL : ∀ u : Nat, u ∈ L ↔
      3 ≤ u ∧ u < n ∧ IsLeaf H u) :
    let S := finiteLeafMeetSupport T (L.image f)
    S.card = n ∧
      (∀ i : Nat, i < n → finiteSupportIndex S i = f i) := by
  classical
  dsimp
  let S := finiteLeafMeetSupport T (L.image f)
  have hn : 3 ≤ n := D.prediary.frame.length_ge_three
  have hSupport :
      S = (Finset.range n).image f :=
    (E.range_eq_image_leafMeetSupport D hn L hL).symm
  have hCard : S.card = n := by
    rw [hSupport]
    rw [Finset.card_image_of_injective _ E.strictMono.injective]
    simp
  refine ⟨hCard, ?_⟩
  intro i hi
  change finiteSupportIndex S i = f i
  rw [hSupport]
  exact finiteSupportIndex_rangeImage_eq n f E.strictMono i hi

/-- All increasing source triples, with both edges and
nonedges, are preserved by the canonical finite support
reindexing obtained from the prescribed leaf image.
This is the crucial finite 'same diary colour' certificate. -/
theorem FiniteMeetEmbedding.canonical_leafSupport_edge_iff
    {H T : Ordered3Graph Nat} {n : Nat} {f : Nat → Nat}
    (D : FiniteRoleDiaryBlock H n)
    (E : FiniteMeetEmbedding H T n f)
    (L : Finset Nat)
    (hL : ∀ u : Nat, u ∈ L ↔
      3 ≤ u ∧ u < n ∧ IsLeaf H u)
    (a b c : Nat) (hab : a < b) (hbc : b < c)
    (hc : c < n) :
    (finiteSupportGraph T
      (finiteLeafMeetSupport T (L.image f))).edge a b c ↔
      H.edge a b c := by
  classical
  let S := finiteLeafMeetSupport T (L.image f)
  obtain ⟨hCard,hIndex⟩ :=
    E.canonical_leafSupport_card_and_index D L hL
  have hsc : c < S.card := by
    rw [hCard]
    exact hc
  have ha : a < n := by omega
  have hb : b < n := by omega
  calc
    (finiteSupportGraph T S).edge a b c ↔
      T.edge (finiteSupportIndex S a)
        (finiteSupportIndex S b)
        (finiteSupportIndex S c) :=
      finiteSupportGraph_edge_iff T S a b c hab hbc hsc
    _ ↔ T.edge (f a) (f b) (f c) := by
      rw [hIndex a ha,hIndex b hb,hIndex c hc]
    _ ↔ H.edge a b c := E.edge_iff a b c hab hbc hc

end DiaryLeafPriority
end ThreeUniformDiaries
