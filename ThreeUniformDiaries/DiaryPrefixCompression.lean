import ThreeUniformDiaries.DiaryAuxTransferWitness

/-!
# Exact type meets in a prefix-preserving compression

Let f be a strictly increasing enumeration of some vertices of an
ordered hypergraph, fixing every vertex below n. A type split strictly
below n cannot change in the induced compressed hypergraph, even when
many vertices are omitted above n. Capped auxiliary meets are also
preserved without any prefix hypothesis.

These are the generic finite-carrier facts used for the pointed
diary envelopes. No claim about arbitrary type envelopes is made.
-/

namespace ThreeUniformDiaries
namespace Ordered3Graph

/-- Hypergraph pulled back along an increasing enumeration of vertices.
Only its values on the finite selected carrier are subsequently used. -/
def pullback (H : Ordered3Graph Nat) (f : Nat → Nat) :
    Ordered3Graph Nat where
  edge a b c := H.edge (f a) (f b) (f c)

private theorem mono_min (f : Nat → Nat) (hf : StrictMono f)
    (a b : Nat) : min (f a) (f b) = f (min a b) := by
  rcases le_total a b with hab | hba
  · simp [min_eq_left hab, min_eq_left (hf.monotone hab)]
  · simp [min_eq_right hba, min_eq_right (hf.monotone hba)]

private theorem mono_nat_ge (f : Nat → Nat) (hf : StrictMono f) :
    ∀ x, x ≤ f x := by
  intro x
  induction x with
  | zero => omega
  | succ x ih =>
    have h : f x + 1 ≤ f (Nat.succ x) :=
      Nat.succ_le_of_lt (hf (Nat.lt_succ_self x))
    exact le_trans (Nat.succ_le_succ ih) h

/-- Below a prefix fixed pointwise by the selected enumeration,
auxiliary type equality is unchanged in the induced hypergraph. -/
theorem pullback_sameAuxTypeBelow_iff
    (H : Ordered3Graph Nat) (f : Nat → Nat) (n k : Nat)
    (hfix : ∀ z, z < n → f z = z)
    (hk : k ≤ n) (a b c d : Nat) :
    (H.pullback f).SameAuxTypeBelow k a b c d ↔
      H.SameAuxTypeBelow k (f a) (f b) (f c) (f d) := by
  constructor
  · intro h z hz
    have heq := hfix z (lt_of_lt_of_le hz hk)
    simpa only [pullback, heq] using (h (a := z) hz)
  · intro h z hz
    have heq := hfix z (lt_of_lt_of_le hz hk)
    simpa only [pullback, heq] using (h (a := z) hz)

/-- Any auxiliary meet strictly before a preserved prefix is exactly
preserved under compression. Unlike a general selected-cut argument,
this needs no assumptions on target vertices omitted above n. -/
theorem pullback_auxMeetLevel_of_lt_prefix
    (H : Ordered3Graph Nat) (f : Nat → Nat) (hf : StrictMono f)
    (n a b c d : Nat)
    (hfix : ∀ z, z < n → f z = z)
    (hbefore : H.auxMeetLevel (f a) (f b) (f c) (f d) < n) :
    (H.pullback f).auxMeetLevel a b c d =
      H.auxMeetLevel (f a) (f b) (f c) (f d) := by
  classical
  let w := H.auxMeetLevel (f a) (f b) (f c) (f d)
  let cap := min a c
  have hmin : min (f a) (f c) = f cap :=
    mono_min f hf a c
  have hboundTarget : w ≤ f cap := by
    simpa only [hmin] using H.auxMeetLevel_le_min (f a) (f b) (f c) (f d)
  have hbound : w ≤ cap := by
    by_contra hn
    have hcaplt : cap < w := by omega
    have hfixCap : f cap = cap := hfix cap (by omega)
    omega
  have hsource : (H.pullback f).SameAuxTypeBelow w a b c d :=
    (H.pullback_sameAuxTypeBelow_iff f n w hfix (by omega) a b c d).mpr
      (H.auxMeetLevel_agree (f a) (f b) (f c) (f d))
  have hlower : w ≤ (H.pullback f).auxMeetLevel a b c d :=
    Nat.le_findGreatest hbound hsource
  have hupper : (H.pullback f).auxMeetLevel a b c d ≤ cap :=
    (H.pullback f).auxMeetLevel_le_min a b c d
  by_cases hcap : w = cap
  · omega
  · have hplus : w + 1 ≤ cap := by omega
    have hplusN : w + 1 ≤ n := by omega
    by_contra hn
    have hsourceMeetGt : w < (H.pullback f).auxMeetLevel a b c d := by
      omega
    have hsourceNext : (H.pullback f).SameAuxTypeBelow (w + 1) a b c d := by
      intro z hz
      exact ((H.pullback f).auxMeetLevel_agree a b c d)
        (lt_of_lt_of_le hz (by omega))
    have htargetNext := (H.pullback_sameAuxTypeBelow_iff f n (w+1)
      hfix hplusN a b c d).mp hsourceNext
    have htargetCap : w + 1 ≤ min (f a) (f c) := by
      rw [hmin]
      exact hplus.trans (mono_nat_ge f hf cap)
    have hw : w + 1 ≤ H.auxMeetLevel (f a) (f b) (f c) (f d) := by
      exact Nat.le_findGreatest
        (P := fun k => H.SameAuxTypeBelow k (f a) (f b) (f c) (f d))
        htargetCap htargetNext
    omega

/-- If the target auxiliary meet is capped at the image of the
smaller pair minimum, its pullback meets at the source cap. -/
theorem pullback_auxMeetLevel_of_target_cap
    (H : Ordered3Graph Nat) (f : Nat → Nat) (hf : StrictMono f)
    (a b c d : Nat)
    (hcap : H.auxMeetLevel (f a) (f b) (f c) (f d) =
      f (min a c)) :
    (H.pullback f).auxMeetLevel a b c d = min a c := by
  classical
  let t := min a c
  have htgt : H.SameAuxTypeBelow (f t) (f a) (f b) (f c) (f d) := by
    rw [← hcap]
    exact H.auxMeetLevel_agree (f a) (f b) (f c) (f d)
  have hsrc : (H.pullback f).SameAuxTypeBelow t a b c d := by
    intro z hz
    have hzT : f z < f t := hf hz
    exact htgt hzT
  have hlow : t ≤ (H.pullback f).auxMeetLevel a b c d :=
    Nat.le_findGreatest (by rfl) hsrc
  have hu := (H.pullback f).auxMeetLevel_le_min a b c d
  omega

end Ordered3Graph
end ThreeUniformDiaries
