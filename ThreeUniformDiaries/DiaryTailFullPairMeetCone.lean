import ThreeUniformDiaries.DiaryTailSingletonTypeCone
import ThreeUniformDiaries.TwoTypeMeetLevel

/-!
# Full pair-type meets are constant in an old-cut singleton-type cone

Consider two ordered pairs with the SAME first coordinates a,c
but potentially different second coordinates:
   (a,b₀), (c,d₀)     versus     (a,b₁), (c,d₁).

If b₀ and b₁ have the same singleton type below B, and likewise
d₀ and d₁, with a,c<B, then their exact capped full two-type
meet levels are equal. The cap is min a c and every
first-coordinate, second-coordinate and auxiliary comparison
below that cap uses only tests whose second test vertex is <B.

For diary extensions the new largest leaf occurs only as the
SECOND member of an increasing ordered leaf pair; this lemma
therefore handles all new S2 generators when a candidate leaf
is replaced by one with the same old-prefix singleton type.

No existence of a replacement leaf or countable embedding
is claimed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- All capped full two-type agreements are invariant under
replacing the SECOND member of either compared pair by a
vertex with the same singleton type over the old prefix. -/
theorem sameTwoTypeBelow_iff_of_second_tail_types
    (K : Ordered3Graph Nat)
    (B l a c b₀ b₁ d₀ d₁ : Nat)
    (haB : a < B) (hcB : c < B) (hl : l ≤ min a c)
    (hb : K.SameOneTypeBelow B b₀ b₁)
    (hd : K.SameOneTypeBelow B d₀ d₁) :
    K.SameTwoTypeBelow l a b₀ c d₀ ↔
      K.SameTwoTypeBelow l a b₁ c d₁ := by
  have hlB : l ≤ B :=
    (hl.trans (min_le_left _ _)).trans haB.le
  have hSecond : K.SameOneTypeBelow l b₀ d₀ ↔
      K.SameOneTypeBelow l b₁ d₁ := by
    constructor
    · intro h x y hxy hyl
      have hyB : y < B := lt_of_lt_of_le hyl hlB
      calc
        K.edge x y b₁ ↔ K.edge x y b₀ := (hb hxy hyB).symm
        _ ↔ K.edge x y d₀ := h hxy hyl
        _ ↔ K.edge x y d₁ := hd hxy hyB
    · intro h x y hxy hyl
      have hyB : y < B := lt_of_lt_of_le hyl hlB
      calc
        K.edge x y b₀ ↔ K.edge x y b₁ := hb hxy hyB
        _ ↔ K.edge x y d₁ := h hxy hyl
        _ ↔ K.edge x y d₀ := (hd hxy hyB).symm
  have hAux : K.SameAuxTypeBelow l a b₀ c d₀ ↔
      K.SameAuxTypeBelow l a b₁ c d₁ := by
    constructor
    · intro h x hx
      have hxa : x < a :=
        lt_of_lt_of_le hx (hl.trans (min_le_left _ _))
      have hxc : x < c :=
        lt_of_lt_of_le hx (hl.trans (min_le_right _ _))
      calc
        K.edge x a b₁ ↔ K.edge x a b₀ := (hb hxa haB).symm
        _ ↔ K.edge x c d₀ := h hx
        _ ↔ K.edge x c d₁ := hd hxc hcB
    · intro h x hx
      have hxa : x < a :=
        lt_of_lt_of_le hx (hl.trans (min_le_left _ _))
      have hxc : x < c :=
        lt_of_lt_of_le hx (hl.trans (min_le_right _ _))
      calc
        K.edge x a b₀ ↔ K.edge x a b₁ := hb hxa haB
        _ ↔ K.edge x c d₁ := h hx
        _ ↔ K.edge x c d₀ := (hd hxc hcB).symm
  constructor
  · rintro ⟨h0,h1,h2⟩
    exact ⟨h0,hSecond.mp h1,hAux.mp h2⟩
  · rintro ⟨h0,h1,h2⟩
    exact ⟨h0,hSecond.mpr h1,hAux.mpr h2⟩

/-- The *numeric* S2 full-pair meet is unchanged in the
same-prefix singleton-type cone. The statement makes no
unwarranted assertion about arbitrary skipped target test levels. -/
theorem twoMeetLevel_eq_of_second_tail_types
    (K : Ordered3Graph Nat)
    (B a c b₀ b₁ d₀ d₁ : Nat)
    (haB : a < B) (hcB : c < B)
    (hb : K.SameOneTypeBelow B b₀ b₁)
    (hd : K.SameOneTypeBelow B d₀ d₁) :
    K.twoMeetLevel a b₀ c d₀ =
      K.twoMeetLevel a b₁ c d₁ := by
  classical
  have hLeft : K.twoMeetLevel a b₀ c d₀ ≤ min a c :=
    K.twoMeetLevel_le_min a b₀ c d₀
  have hRight : K.twoMeetLevel a b₁ c d₁ ≤ min a c :=
    K.twoMeetLevel_le_min a b₁ c d₁
  have hLR : K.twoMeetLevel a b₀ c d₀ ≤
      K.twoMeetLevel a b₁ c d₁ := by
    apply Nat.le_findGreatest hLeft
    exact (sameTwoTypeBelow_iff_of_second_tail_types
      K B _ a c b₀ b₁ d₀ d₁ haB hcB hLeft hb hd).mp
        (K.twoMeetLevel_agree a b₀ c d₀)
  have hRL : K.twoMeetLevel a b₁ c d₁ ≤
      K.twoMeetLevel a b₀ c d₀ := by
    apply Nat.le_findGreatest hRight
    exact (sameTwoTypeBelow_iff_of_second_tail_types
      K B _ a c b₀ b₁ d₀ d₁ haB hcB hRight hb hd).mpr
        (K.twoMeetLevel_agree a b₁ c d₁)
  exact Nat.le_antisymm hLR hRL

end DiaryLeafPriority
end ThreeUniformDiaries
