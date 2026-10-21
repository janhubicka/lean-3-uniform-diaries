import ThreeUniformDiaries.DiaryFiniteBoundedUniversality
import ThreeUniformDiaries.DiaryFiniteCanonicalFlipPullback

/-!
# Finite tables for bounded protected diary embeddings

FiniteBoundedMeetEmbedding is currently stated for a *total*
map Nat -> Nat, required to be strictly increasing even outside
its bounded source domain [0,n). For finite exhaustive search,
the only relevant entries are its first n values, which lie in
Fin k by the verified bounded-image condition.

A strictly increasing finite table Fin n -> Fin k extends to
a strictly increasing total map by setting f(u)=k+(u-n)
for u >= n. The extension agrees with its table on the
finite source interval. Every field of a genuine finite meet
embedding, including exact mixed singleton and ordered-pair
meets, is invariant under changes to the unused tail.

Thus existence of a bounded protected embedding is EQUIVALENT
to a quantifier over the genuinely finite function type
Fin n -> Fin k, with one explicit canonical extension.
This is a correct finite candidate space; it is not an
algorithm establishing the missing absorption theorem.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Extend a bounded finite map by a strictly increasing tail
starting at the first vertex OUTSIDE the finite target. -/
def extendFiniteBoundedMap (n k : Nat)
    (g : Fin n → Fin k) (u : Nat) : Nat :=
  if h : u < n then (g ⟨u,h⟩).val else k + (u - n)

/-- The finite part of the extension is the prescribed table. -/
theorem extendFiniteBoundedMap_apply_lt
    (n k : Nat) (g : Fin n → Fin k)
    (u : Nat) (hu : u < n) :
    extendFiniteBoundedMap n k g u = (g ⟨u,hu⟩).val := by
  simp only [extendFiniteBoundedMap, dif_pos hu]

/-- Order preservation on the finite table gives a genuine
strictly monotone TOTAL map; the tail begins at k, beyond
all finite image values. -/
theorem extendFiniteBoundedMap_strictMono
    (n k : Nat) (g : Fin n → Fin k)
    (hg : StrictMono g) :
    StrictMono (extendFiniteBoundedMap n k g) := by
  intro a b hab
  by_cases ha : a < n
  · by_cases hb : b < n
    · simp only [extendFiniteBoundedMap, dif_pos ha, dif_pos hb]
      exact hg (show (⟨a,ha⟩ : Fin n) < ⟨b,hb⟩ from hab)
    · simp only [extendFiniteBoundedMap, dif_pos ha, dif_neg hb]
      have hRange : (g ⟨a,ha⟩).val < k := (g ⟨a,ha⟩).isLt
      omega
  · have hb : ¬ b < n := by omega
    simp only [extendFiniteBoundedMap, dif_neg ha, dif_neg hb]
    omega

/-- Replacing the artificial tail of an embedding map changes
no edge, role or numerical meet field from the source diary.
The replacement must remain strictly increasing and agree on
the actual bounded source interval. -/
theorem FiniteBoundedMeetEmbedding.of_same_finite_prefix
    {A B : Ordered3Graph Nat} {n k : Nat}
    {f g : Nat → Nat}
    (E : FiniteBoundedMeetEmbedding A B n k f)
    (hn : 3 ≤ n)
    (hg : StrictMono g)
    (hAgree : ∀ u : Nat, u < n → g u = f u) :
    FiniteBoundedMeetEmbedding A B n k g := by
  refine ⟨{
    strictMono := hg
    marker_zero := ?_
    marker_one := ?_
    marker_two := ?_
    edge_iff := ?_
    leaf_iff := ?_
    oneSplit_iff := ?_
    twoSplit_iff := ?_
    oneMeet := ?_
    twoMeet := ?_
  }, ?_⟩
  · rw [hAgree 0 (by omega)]
    exact E.toMeetEmbedding.marker_zero
  · rw [hAgree 1 (by omega)]
    exact E.toMeetEmbedding.marker_one
  · rw [hAgree 2 (by omega)]
    exact E.toMeetEmbedding.marker_two
  · intro a b c hab hbc hcn
    have han : a < n := by omega
    have hbn : b < n := by omega
    rw [hAgree a han, hAgree b hbn, hAgree c hcn]
    exact E.toMeetEmbedding.edge_iff a b c hab hbc hcn
  · intro u hu3 hun
    rw [hAgree u hun]
    exact E.toMeetEmbedding.leaf_iff u hu3 hun
  · intro u hu3 hun
    rw [hAgree u hun]
    exact E.toMeetEmbedding.oneSplit_iff u hu3 hun
  · intro u hu3 hun
    rw [hAgree u hun]
    exact E.toMeetEmbedding.twoSplit_iff u hu3 hun
  · intro u v hu3 hun hv3 hvn
    have hMeetBound : A.oneMeetLevel u v < n := by
      have hLe := A.oneMeetLevel_le_min u v
      omega
    rw [hAgree u hun, hAgree v hvn,
      hAgree (A.oneMeetLevel u v) hMeetBound]
    exact E.toMeetEmbedding.oneMeet u v hu3 hun hv3 hvn
  · intro a b c d hab hcd ha3 han hb3 hbn hc3 hcn hd3 hdn
    have hMeetBound : A.twoMeetLevel a b c d < n := by
      have hLe := A.twoMeetLevel_le_min a b c d
      omega
    rw [hAgree a han,hAgree b hbn,hAgree c hcn,hAgree d hdn,
      hAgree (A.twoMeetLevel a b c d) hMeetBound]
    exact E.toMeetEmbedding.twoMeet a b c d hab hcd
      ha3 han hb3 hbn hc3 hcn hd3 hdn
  · intro u hu
    rw [hAgree u hu]
    exact E.image_bound u hu

/-- Every bounded protected embedding admits a finite table whose
canonical extension is still a full protected bounded embedding.
All numerical mixed meets survive tail normalisation. -/
theorem FiniteBoundedMeetEmbedding.exists_finite_table
    {A B : Ordered3Graph Nat} {n k : Nat} {f : Nat → Nat}
    (E : FiniteBoundedMeetEmbedding A B n k f)
    (hn : 3 ≤ n) :
    ∃ g : Fin n → Fin k,
      StrictMono g ∧
      FiniteBoundedMeetEmbedding A B n k
        (extendFiniteBoundedMap n k g) ∧
      (∀ u : Nat, u < n →
        extendFiniteBoundedMap n k g u = f u) := by
  let g : Fin n → Fin k :=
    fun x => ⟨f x.val,E.image_bound x.val x.isLt⟩
  have hg : StrictMono g := by
    intro x y hxy
    exact E.toMeetEmbedding.strictMono hxy
  have hAgree : ∀ u : Nat, u < n →
      extendFiniteBoundedMap n k g u = f u := by
    intro u hu
    rw [extendFiniteBoundedMap_apply_lt n k g u hu]
    rfl
  exact ⟨g,hg,
    E.of_same_finite_prefix hn
      (extendFiniteBoundedMap_strictMono n k g hg) hAgree,
    hAgree⟩

/-- Existence of a bounded all-meet preserving finite diary
embedding is exactly a FINITE-TABLE existential problem.
All candidate tables live in the finite type Fin n -> Fin k. -/
theorem exists_boundedMeetEmbedding_iff_finite_table
    {A B : Ordered3Graph Nat} {n k : Nat}
    (hn : 3 ≤ n) :
    (∃ f : Nat → Nat, FiniteBoundedMeetEmbedding A B n k f) ↔
      ∃ g : Fin n → Fin k,
        StrictMono g ∧
        FiniteBoundedMeetEmbedding A B n k
          (extendFiniteBoundedMap n k g) := by
  constructor
  · rintro ⟨f,Ef⟩
    obtain ⟨g,hg,hE,_⟩ := Ef.exists_finite_table hn
    exact ⟨g,hg,hE⟩
  · rintro ⟨g,_hg,hE⟩
    exact ⟨extendFiniteBoundedMap n k g,hE⟩

end DiaryLeafPriority
end ThreeUniformDiaries
