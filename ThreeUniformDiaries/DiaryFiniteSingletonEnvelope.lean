import ThreeUniformDiaries.DiarySelectedCarrierClosure
import ThreeUniformDiaries.DiaryEnvelopeMinimality
import ThreeUniformDiaries.DiarySingletonEnvelopeTransfer

/-!
# Native finite singleton envelopes for lower-bound stabilisation

A singleton envelope at the protected cut n is the full prefix
[0,n) together with one selected vertex a ≥ n. Its canonical
increasing enumeration may skip arbitrarily many target vertices,
but the omitted levels do not change ANY singleton or auxiliary
meet on its n+1 real vertices.

This is the single-tail analogue of the already checked two-tail
and three-tail pointed diary envelopes. No diary-specific role
axiom is needed. The resulting least meet-closed carrier supports
the singleton-type colour of the lower-bound stabilisation proof.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Include one selected vertex immediately after a protected
prefix, then continue with consecutive target vertices. -/
def oneTailInsertion (n a t : Nat) : Nat :=
  if t < n then t else a + (t - n)

theorem oneTailInsertion_strictMono
    (n a : Nat) (hna : n ≤ a) :
    StrictMono (oneTailInsertion n a) := by
  apply strictMono_nat_of_lt_succ
  intro t
  unfold oneTailInsertion
  split_ifs <;> omega

theorem oneTailInsertion_fix_prefix
    (n a t : Nat) (ht : t < n) :
    oneTailInsertion n a t = t := by
  simp [oneTailInsertion, ht]

theorem oneTailInsertion_endpoint (n a : Nat) :
    oneTailInsertion n a n = a := by
  simp [oneTailInsertion]

theorem oneTailInsertion_carrier_iff
    (n a x : Nat) :
    x ∈ selectedCarrier (oneTailInsertion n a) (n+1) ↔
      x < n ∨ x = a := by
  constructor
  · rintro ⟨t, ht, hval⟩
    by_cases hpre : t < n
    · left
      rw [oneTailInsertion_fix_prefix n a t hpre] at hval
      omega
    · right
      have heq : t = n := by omega
      rw [heq, oneTailInsertion_endpoint] at hval
      exact hval.symm
  · intro h
    rcases h with hpre | ha
    · exact ⟨x, by omega, oneTailInsertion_fix_prefix n a x hpre⟩
    · exact ⟨n, by omega,
        (oneTailInsertion_endpoint n a).trans ha.symm⟩

/-- Every singleton meet of two actual vertices in a prefix-plus-one
carrier is preserved exactly by the induced enumeration. -/
theorem one_tail_oneMeet_preserved
    (K : Ordered3Graph Nat) (f : Nat → Nat) (hf : StrictMono f)
    (n : Nat) (hfix : ∀ t < n, f t = t)
    (u v : Nat) (hu : u < n+1) (hv : v < n+1) :
    K.oneMeetLevel (f u) (f v) =
      f ((K.pullback f).oneMeetLevel u v) := by
  classical
  by_cases heq : u = v
  · subst v
    simp only [oneMeetLevel_self_full]
  · have hpre : min u v < n := by
      by_contra hn
      have hnu : n ≤ u := by omega
      have hnv : n ≤ v := by omega
      have hU : u = n := by omega
      have hV : v = n := by omega
      exact heq (hU.trans hV.symm)
    have hmin : min (f u) (f v) = f (min u v) := by
      rcases le_total u v with huv | hvu
      · simp [min_eq_left huv, min_eq_left (hf.monotone huv)]
      · simp [min_eq_right hvu, min_eq_right (hf.monotone hvu)]
    have hearly : K.oneMeetLevel (f u) (f v) < n := by
      have hbound := K.oneMeetLevel_le_min (f u) (f v)
      rw [hmin, hfix (min u v) hpre] at hbound
      omega
    have hsrc := K.pullback_oneMeetLevel_of_lt_prefix
      f hf n u v hfix hearly
    have hsrcLt : (K.pullback f).oneMeetLevel u v < n := by
      rw [hsrc]
      exact hearly
    calc
      K.oneMeetLevel (f u) (f v) =
        (K.pullback f).oneMeetLevel u v := hsrc.symm
      _ = f ((K.pullback f).oneMeetLevel u v) :=
        (hfix _ hsrcLt).symm

/-- There is no pair entirely outside a prefix-plus-one carrier.
Every auxiliary pair meet therefore splits within the fixed prefix
or is capped there. -/
theorem one_tail_auxMeet_preserved
    (K : Ordered3Graph Nat) (f : Nat → Nat) (hf : StrictMono f)
    (n : Nat) (hfix : ∀ t < n, f t = t)
    (a b c d : Nat) (hab : a < b) (hcd : c < d)
    (hb : b < n+1) (hd : d < n+1) :
    K.auxMeetLevel (f a) (f b) (f c) (f d) =
      f ((K.pullback f).auxMeetLevel a b c d) := by
  apply K.pullback_auxMeetLevel_preserved_of_early_distinctions
    f hf n (n+1) hfix
  · intro u₀ u₁ v₀ v₁ hu hv hU hV hnu hnv hne
    omega
  · exact hab
  · exact hcd
  · exact hb
  · exact hd

/-- Complete actual finite ATR meet preservation for a
prefix-plus-one selected enumeration. -/
theorem one_tail_ATR_finite
    (K : Ordered3Graph Nat) (f : Nat → Nat) (hf : StrictMono f)
    (n : Nat) (hfix : ∀ t < n, f t = t) :
    (∀ u v, u < n+1 → v < n+1 →
      K.oneMeetLevel (f u) (f v) =
        f ((K.pullback f).oneMeetLevel u v)) ∧
    (∀ a b c d, a < b → c < d →
      b < n+1 → d < n+1 →
      K.auxMeetLevel (f a) (f b) (f c) (f d) =
        f ((K.pullback f).auxMeetLevel a b c d)) := by
  constructor
  · intro u v hu hv
    exact K.one_tail_oneMeet_preserved f hf n hfix u v hu hv
  · intro a b c d hab hcd hb hd
    exact K.one_tail_auxMeet_preserved f hf n hfix
      a b c d hab hcd hb hd

/-- A native singleton type-envelope with the whole fixed prefix
and exactly one distinguished final vertex. -/
structure FiniteSingletonEnvelope
    (K : Ordered3Graph Nat) (n a : Nat) where
  enumerate : Nat → Nat
  strictMono : StrictMono enumerate
  protected_prefix : ∀ t < n, enumerate t = t
  endpoint : enumerate n = a
  singleton_meets :
    ∀ u v, u < n+1 → v < n+1 →
      K.oneMeetLevel (enumerate u) (enumerate v) =
        enumerate ((K.pullback enumerate).oneMeetLevel u v)
  auxiliary_meets :
    ∀ u v x y, u < v → x < y → v < n+1 → y < n+1 →
      K.auxMeetLevel (enumerate u) (enumerate v)
        (enumerate x) (enumerate y) =
        enumerate ((K.pullback enumerate).auxMeetLevel u v x y)
  minimal :
    K.IsMinimalMeetEnvelope n a a
      (selectedCarrier enumerate (n+1))

namespace FiniteSingletonEnvelope

variable {K : Ordered3Graph Nat} {n a : Nat}

/-- The actual finite induced enumeration, including only
the protected prefix and its one terminal vertex. -/
def induced (E : FiniteSingletonEnvelope K n a) :
    Ordered3Graph Nat := K.pullback E.enumerate

/-- Existence of the least singleton envelope at any target vertex
a ≥ n, with no diary or other structural assumptions. -/
def ofVertex (K : Ordered3Graph Nat) (n a : Nat) (hna : n ≤ a) :
    FiniteSingletonEnvelope K n a := by
  let f : Nat → Nat := oneTailInsertion n a
  have hf : StrictMono f :=
    oneTailInsertion_strictMono n a hna
  have hfix : ∀ t < n, f t = t := by
    intro t ht
    exact oneTailInsertion_fix_prefix n a t ht
  have hlast : f n = a := oneTailInsertion_endpoint n a
  obtain ⟨hone, haux⟩ := K.one_tail_ATR_finite f hf n hfix
  have hclosed : K.IsMeetClosed (selectedCarrier f (n+1)) :=
    K.selectedCarrier_meet_closed_of_ATR
      f hf (n+1) hone haux
  have hmin : K.IsMinimalMeetEnvelope n a a
      (selectedCarrier f (n+1)) := by
    refine ⟨hclosed, ?_, ?_, ?_, ?_⟩
    · intro t ht
      exact ⟨t, by omega, hfix t ht⟩
    · exact ⟨n, by omega, hlast⟩
    · exact ⟨n, by omega, hlast⟩
    · intro T hT hp ha hb x hx
      rcases (oneTailInsertion_carrier_iff n a x).mp hx with hpre | hleaf
      · exact hp x hpre
      · simpa only [hleaf] using ha
  exact {
    enumerate := f
    strictMono := hf
    protected_prefix := hfix
    endpoint := hlast
    singleton_meets := hone
    auxiliary_meets := haux
    minimal := hmin
  }

end FiniteSingletonEnvelope
end Ordered3Graph
end ThreeUniformDiaries
