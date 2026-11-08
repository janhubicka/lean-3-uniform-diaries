import ThreeUniformDiaries.DiaryLiteralOldPrefixTypeMeetTransport
import ThreeUniformDiaries.TwoTypeMeetLevel

/-!
# Track B: literal old-prefix agreement preserves FULL pair types

The finite old-prefix agreement theorem already transfers all
marker-coded roles, exact singleton type tests, and singleton meets.
Here we verify the full two-coordinate and AUXILIARY type agreement,
including the capped exact numerical full 2-type meet.

This is an edge-only theorem about genuine old source vertices.
No global RoleDiary assumption on a zero-extended finite graph,
no false arbitrary old-cut type preservation under non-surjective
embeddings, and no countable source flip conclusion are used.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {A C : Ordered3Graph Nat} {n : Nat}

/-- For two genuinely OLD ordered pairs, every auxiliary test
edge(z,u0,u1) has its last coordinate u1 < n, so literal
old-prefix agreement transfers both edges and nonedges at
every cut, without a condition on the cut itself. -/
theorem sameAuxTypeBelow_iff_of_literalOldPrefix
    (h : LiteralOldPrefixAgreement A C n)
    (u₀ u₁ v₀ v₁ l : Nat)
    (hu₁ : u₁ < n) (hv₁ : v₁ < n) :
    A.SameAuxTypeBelow l u₀ u₁ v₀ v₁ ↔
      C.SameAuxTypeBelow l u₀ u₁ v₀ v₁ := by
  constructor
  · intro hA z hz
    have hU := h z u₀ u₁ hu₁
    have hV := h z v₀ v₁ hv₁
    exact hU.symm.trans ((hA hz).trans hV)
  · intro hC z hz
    have hU := h z u₀ u₁ hu₁
    have hV := h z v₀ v₁ hv₁
    exact hU.trans ((hC hz).trans hV.symm)

/-- The capped AUXILIARY pair meet is numerically identical on
old genuine ordered-pair vertices, including the marker cap. -/
theorem auxMeetLevel_eq_of_literalOldPrefix
    (h : LiteralOldPrefixAgreement A C n)
    (u₀ u₁ v₀ v₁ : Nat)
    (hu₁ : u₁ < n) (hv₁ : v₁ < n) :
    A.auxMeetLevel u₀ u₁ v₀ v₁ =
      C.auxMeetLevel u₀ u₁ v₀ v₁ := by
  have hTypes (l : Nat) :
      A.SameAuxTypeBelow l u₀ u₁ v₀ v₁ ↔
      C.SameAuxTypeBelow l u₀ u₁ v₀ v₁ :=
    sameAuxTypeBelow_iff_of_literalOldPrefix
      h u₀ u₁ v₀ v₁ l hu₁ hv₁
  apply le_antisymm
  · have hAgree : C.SameAuxTypeBelow
        (A.auxMeetLevel u₀ u₁ v₀ v₁) u₀ u₁ v₀ v₁ :=
      (hTypes _).mp (A.auxMeetLevel_agree u₀ u₁ v₀ v₁)
    exact Nat.le_findGreatest
      (A.auxMeetLevel_le_min u₀ u₁ v₀ v₁) hAgree
  · have hAgree : A.SameAuxTypeBelow
        (C.auxMeetLevel u₀ u₁ v₀ v₁) u₀ u₁ v₀ v₁ :=
      (hTypes _).mpr (C.auxMeetLevel_agree u₀ u₁ v₀ v₁)
    exact Nat.le_findGreatest
      (C.auxMeetLevel_le_min u₀ u₁ v₀ v₁) hAgree

/-- Full two-types are the product of two old singleton types
and the old auxiliary pair type, with literal agreement at
ALL cuts. -/
theorem sameTwoTypeBelow_iff_of_literalOldPrefix
    (h : LiteralOldPrefixAgreement A C n)
    (u₀ u₁ v₀ v₁ l : Nat)
    (hu₀ : u₀ < n) (hu₁ : u₁ < n)
    (hv₀ : v₀ < n) (hv₁ : v₁ < n) :
    A.SameTwoTypeBelow l u₀ u₁ v₀ v₁ ↔
      C.SameTwoTypeBelow l u₀ u₁ v₀ v₁ := by
  constructor
  · rintro ⟨hFirst,hSecond,hAux⟩
    exact ⟨(sameOneTypeBelow_iff_of_literalOldPrefix
        h u₀ v₀ l hu₀ hv₀).mp hFirst,
      (sameOneTypeBelow_iff_of_literalOldPrefix
        h u₁ v₁ l hu₁ hv₁).mp hSecond,
      (sameAuxTypeBelow_iff_of_literalOldPrefix
        h u₀ u₁ v₀ v₁ l hu₁ hv₁).mp hAux⟩
  · rintro ⟨hFirst,hSecond,hAux⟩
    exact ⟨(sameOneTypeBelow_iff_of_literalOldPrefix
        h u₀ v₀ l hu₀ hv₀).mpr hFirst,
      (sameOneTypeBelow_iff_of_literalOldPrefix
        h u₁ v₁ l hu₁ hv₁).mpr hSecond,
      (sameAuxTypeBelow_iff_of_literalOldPrefix
        h u₀ u₁ v₀ v₁ l hu₁ hv₁).mpr hAux⟩

/-- EXACT numerical full pair meet of all old ordered pairs
is conserved by literal finite-prefix agreement. No type
gap or omitted-vertex premise is required because all test
vertices and pair coordinates are literally old. -/
theorem twoMeetLevel_eq_of_literalOldPrefix
    (h : LiteralOldPrefixAgreement A C n)
    (u₀ u₁ v₀ v₁ : Nat)
    (hu₀ : u₀ < n) (hu₁ : u₁ < n)
    (hv₀ : v₀ < n) (hv₁ : v₁ < n) :
    A.twoMeetLevel u₀ u₁ v₀ v₁ =
      C.twoMeetLevel u₀ u₁ v₀ v₁ := by
  have hTypes (l : Nat) :
      A.SameTwoTypeBelow l u₀ u₁ v₀ v₁ ↔
      C.SameTwoTypeBelow l u₀ u₁ v₀ v₁ :=
    sameTwoTypeBelow_iff_of_literalOldPrefix
      h u₀ u₁ v₀ v₁ l hu₀ hu₁ hv₀ hv₁
  apply le_antisymm
  · have hAgree : C.SameTwoTypeBelow
        (A.twoMeetLevel u₀ u₁ v₀ v₁) u₀ u₁ v₀ v₁ :=
      (hTypes _).mp (A.twoMeetLevel_agree u₀ u₁ v₀ v₁)
    exact Nat.le_findGreatest
      (A.twoMeetLevel_le_min u₀ u₁ v₀ v₁) hAgree
  · have hAgree : A.SameTwoTypeBelow
        (C.twoMeetLevel u₀ u₁ v₀ v₁) u₀ u₁ v₀ v₁ :=
      (hTypes _).mpr (C.twoMeetLevel_agree u₀ u₁ v₀ v₁)
    exact Nat.le_findGreatest
      (C.twoMeetLevel_le_min u₀ u₁ v₀ v₁) hAgree

/-- Exact conservation of ALL old numerical singleton and
full ordered-pair meets, including mixed split/leaf tuples.
The conclusion is not restricted to leaf coordinates. -/
theorem all_numeric_meets_eq_of_literalOldPrefix
    (h : LiteralOldPrefixAgreement A C n) :
    (∀ u v : Nat, u < n → v < n →
      A.oneMeetLevel u v = C.oneMeetLevel u v) ∧
    (∀ a b c d : Nat, a < n → b < n → c < n → d < n →
      A.twoMeetLevel a b c d = C.twoMeetLevel a b c d) := by
  constructor
  · intro u v hu hv
    exact oneMeetLevel_eq_of_literalOldPrefix h u v hu hv
  · intro a b c d ha hb hc hd
    exact twoMeetLevel_eq_of_literalOldPrefix
      h a b c d ha hb hc hd

end DiaryLeafPriority
end ThreeUniformDiaries
