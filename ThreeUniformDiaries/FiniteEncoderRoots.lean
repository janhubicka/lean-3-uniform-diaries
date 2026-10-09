import ThreeUniformDiaries.FiniteEnumMeetClosure
import ThreeUniformDiaries.FiniteOneMeetClosure
import ThreeUniformDiaries.FiniteAuxMeetClosure
import ThreeUniformDiaries.TypeNodePrefix

/-!
# The initial root of each finite strong-encoding coordinate

For the no-fixed-prefix case n=0, the first ambient selected
level may be e(0)>0. A genuine strong subtree must nevertheless
have exactly one root there. Aux-type-respect forces all 1-types
and all auxiliary pair types over e(0) to coincide, since their
original types over cut zero are vacuously equal. This supplies
the distinguished common root of the selected E1 and E2^- pictures.
E0 is simply the chain of target enumeration prefixes.

These root lemmas supply the base case of finite strong-subtree
completion without forcing e(0)=0.
-/

namespace ThreeUniformDiaries
namespace EnumNode

/-- Any two selected vertices have identical singleton types below
the first image e(0), because source cut zero has no edge tests. -/
theorem oneTypes_agree_at_first_image
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (e : Ordered3Graph.Embedding A.toOrdered3Graph H.toOrdered3Graph)
    (haux : e.AuxTypeRespecting) (u v : Nat) :
    H.oneType (e 0) (e u) = H.oneType (e 0) (e v) := by
  have hzero : A.toOrdered3Graph.SameOneTypeBelow 0 u v := by
    intro a b hab hb
    omega
  have htarget := (haux.one 0 u v (Nat.zero_le u)
    (Nat.zero_le v)).mp hzero
  exact (H.oneType_eq_iff_sameOneTypeBelow).mpr htarget

/-- Every pair of ordered source pairs has the same auxiliary type
over the initial cut e(0). -/
theorem auxTypes_agree_at_first_image
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (e : Ordered3Graph.Embedding A.toOrdered3Graph H.toOrdered3Graph)
    (haux : e.AuxTypeRespecting)
    (u₀ u₁ v₀ v₁ : Nat)
    (hu : u₀ < u₁) (hv : v₀ < v₁) :
    H.auxType (e 0) (e u₀) (e u₁) =
      H.auxType (e 0) (e v₀) (e v₁) := by
  have hzero : A.toOrdered3Graph.SameAuxTypeBelow
      0 u₀ u₁ v₀ v₁ := by
    intro a ha
    omega
  have htarget := (haux.aux 0 u₀ u₁ v₀ v₁
    (Nat.zero_le u₀) hu (Nat.zero_le v₀) hv).mp hzero
  exact (H.auxType_eq_iff_sameAuxTypeBelow).mpr htarget

/-- The E1 coordinate at n=0 has one distinguished first-level root
below every prescribed singleton type node. -/
theorem finiteOneCandidate_root_zero
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (e : Ordered3Graph.Embedding A.toOrdered3Graph H.toOrdered3Graph)
    (haux : e.AuxTypeRespecting) (hm : 0 < m) :
    ∃ r : CoordNode,
      finiteOneCandidate A H e 0 r ∧
      CoordNode.level r = e 0 ∧
      ∀ x : CoordNode,
        finiteOneCandidate A H e 0 x → r ≤ x := by
  let r := CoordNode.one (e 0) (H.oneType (e 0) (e 0))
  refine ⟨r, ?_, rfl, ?_⟩
  · right
    exact ⟨0, 0, le_rfl, le_rfl, hm, rfl⟩
  · intro x hx
    rcases hx with ⟨k, B, hk, heq⟩ |
        ⟨i, v, hni, hiv, hvm, heq⟩
    · omega
    · subst x
      have hlei : e 0 ≤ e i :=
        e.strictMono.monotone (Nat.zero_le i)
      refine ⟨hlei, ?_⟩
      change CoordNode.one (e 0)
          ((H.oneType (e i) (e v)).truncate (e 0)) =
        CoordNode.one (e 0) (H.oneType (e 0) (e 0))
      rw [H.oneType_truncate (u := e v) hlei]
      rw [A.oneTypes_agree_at_first_image H e haux v 0]

/-- For m>1 the E2^- candidate set at n=0 likewise has one common
root at e(0), witnessed by the pair (0,1). -/
theorem finiteAuxCandidate_root_zero
    {m N : Nat} (A : EnumNode m) (H : EnumNode N)
    (e : Ordered3Graph.Embedding A.toOrdered3Graph H.toOrdered3Graph)
    (haux : e.AuxTypeRespecting) (hm : 1 < m) :
    ∃ r : CoordNode,
      finiteAuxCandidate A H e 0 r ∧
      CoordNode.level r = e 0 ∧
      ∀ x : CoordNode,
        finiteAuxCandidate A H e 0 x → r ≤ x := by
  let r := CoordNode.aux (e 0)
    (H.auxType (e 0) (e 0) (e 1))
  refine ⟨r, ?_, rfl, ?_⟩
  · right
    exact ⟨0, 0, 1, le_rfl, le_rfl,
      Nat.zero_lt_one, hm, rfl⟩
  · intro x hx
    rcases hx with ⟨k, B, hk, heq⟩ |
        ⟨i, u₀, u₁, hni, hiu, hu, hum, heq⟩
    · omega
    · subst x
      have hlei : e 0 ≤ e i :=
        e.strictMono.monotone (Nat.zero_le i)
      refine ⟨hlei, ?_⟩
      change CoordNode.aux (e 0)
          ((H.auxType (e i) (e u₀) (e u₁)).truncate (e 0)) =
        CoordNode.aux (e 0) (H.auxType (e 0) (e 0) (e 1))
      rw [H.auxType_truncate (u := e u₀) (v := e u₁) hlei]
      rw [A.auxTypes_agree_at_first_image H e haux
        u₀ u₁ 0 1 hu Nat.zero_lt_one]

/-- Enumeration-coordinate prefixes form a rooted chain with
root H|_{e(0)}, even when the first selected level is positive. -/
theorem finiteEnumCandidate_root_zero
    {N : Nat} (H : EnumNode N) (e : Nat → Nat)
    (he : StrictMono e) (m : Nat) (hm : 0 < m) :
    ∃ r : CoordNode,
      finiteEnumCandidate H e 0 m r ∧
      CoordNode.level r = e 0 ∧
      ∀ x : CoordNode,
        finiteEnumCandidate H e 0 m x → r ≤ x := by
  let r := CoordNode.enum (e 0) (H.truncate (e 0))
  refine ⟨r, ?_, rfl, ?_⟩
  · right
    exact ⟨0, le_rfl, hm, rfl⟩
  · intro x hx
    rcases hx with ⟨k, B, hk, heq⟩ | ⟨i, hni, him, heq⟩
    · omega
    · subst x
      have hlei : e 0 ≤ e i := he.monotone (Nat.zero_le i)
      refine ⟨hlei, ?_⟩
      change CoordNode.enum (e 0)
          ((H.truncate (e i)).truncate (e 0)) =
        CoordNode.enum (e 0) (H.truncate (e 0))
      exact congrArg (CoordNode.enum (e 0))
        (H.truncate_truncate hlei)

end EnumNode
end ThreeUniformDiaries
