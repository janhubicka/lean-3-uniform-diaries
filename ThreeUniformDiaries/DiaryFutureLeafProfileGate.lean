import ThreeUniformDiaries.DiaryCofinalStageRestrictions

/-!
# The missing old-split profile constraint in diary fusion

The unordered generic leaf-range theorem controls edges on triples
OF LEAVES. An extension of a prescribed finite diary support must
also decide incidences of each fresh source leaf with previously
embedded marker/split pairs. These are not consequences of genericity
of the leaf hypergraph alone.

We isolate a literal finite-support old-pair profile. Every genuinely
coherent countable diary family necessarily realizes it in the
prescribed leaf range. The theorem does NOT assert that a fresh
profile realization exists for arbitrary prescribed finite maps.
No extra type-transport or unproved relative absorber is assumed.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The exact required incidences for adding a future source
leaf u to a fixed finite stage map f, including marker/split pairs.
All tests are source increasing triples x<y<u. -/
structure OldPairLeafExtensionProfile
    (H K : Ordered3Graph Nat) (F : Nat → Nat)
    (m : Nat) (f : Nat → Nat)
    (u v : Nat) : Prop where
  leaf : IsLeaf K v
  range : ∃ t : Nat, v = F t
  later : ∀ x : Nat,
    x ∈ countableDiaryFiniteSupport H m →
    x < u → f x < v
  induced_old_pairs : ∀ x y : Nat,
    x ∈ countableDiaryFiniteSupport H m →
    y ∈ countableDiaryFiniteSupport H m →
    x < y → y < u →
    (K.edge (f x) (f y) v ↔ H.edge x y u)

namespace OldPairLeafExtensionProfile

variable {H K : Ordered3Graph Nat} {F : Nat → Nat}
variable {m u v : Nat} {f : Nat → Nat}

/-- The old-pair profile contains the exact 1-split orientation
incidence with marker zero. This is not a leaf-only edge test. -/
theorem one_split_marker_incidence
    (P : OldPairLeafExtensionProfile H K F m f u v)
    (s : Nat)
    (hs : s ∈ countableDiaryFiniteSupport H m)
    (hSplit : IsOneSplit H s) (hsu : s < u) :
    K.edge (f 0) (f s) v ↔ H.edge 0 s u := by
  have h0 : 0 ∈ countableDiaryFiniteSupport H m :=
    mem_finiteLeafMeetSupport_marker H
      (countableDiaryLeafPrefix H m) 0 (by omega)
  exact P.induced_old_pairs 0 s h0 hs (by omega) hsu

/-- Likewise, the profile includes the 2-split/earlier-leaf
incidences; genericity of the underlying leaf triples does not
automatically control these mixed triples. -/
theorem two_split_old_leaf_incidence
    (P : OldPairLeafExtensionProfile H K F m f u v)
    (s a : Nat)
    (hs : s ∈ countableDiaryFiniteSupport H m)
    (ha : a ∈ countableDiaryFiniteSupport H m)
    (hsa : s < a) (hau : a < u) :
    K.edge (f s) (f a) v ↔ H.edge s a u :=
  P.induced_old_pairs s a hs ha hsa hau

end OldPairLeafExtensionProfile

namespace CoherentCofinalDiarySupportMaps

variable {H K : Ordered3Graph Nat} {DH : RoleDiary H}

/-- A globally coherent countable diary embedding automatically
realises EVERY old-pair profile by its chosen image of the future
leaf. Consequently this profile is NECESSARY for any proposed
local reservoir or relative extension theorem. -/
theorem future_leaf_old_pair_profile
    (P : CoherentCofinalDiarySupportMaps DH K)
    (F : Nat → Nat)
    (hRange : ∀ m u : Nat,
      u ∈ countableDiaryFiniteSupport H m →
      IsLeaf H u → ∃ t : Nat, P.map m u = F t)
    (m u : Nat) (hLeaf : IsLeaf H u) :
    ∃ v : Nat,
      OldPairLeafExtensionProfile H K F m (P.map m) u v := by
  refine ⟨P.limit u, ?_⟩
  refine {
    leaf := P.limit_is_diaryPreembedding.leaf_role u hLeaf
    range := P.limit_leaf_range F hRange u hLeaf
    later := ?_
    induced_old_pairs := ?_
  }
  · intro x hx hxu
    have hs := P.limit_is_diaryPreembedding.strictMono hxu
    rw [P.limit_eq_stage m x hx] at hs
    exact hs
  · intro x y hx hy hxy hyu
    have hs := P.limit_induced_all_triples x y u hxy hyu
    rw [P.limit_eq_stage m x hx,
        P.limit_eq_stage m y hy] at hs
    exact hs.symm

end CoherentCofinalDiarySupportMaps
end DiaryLeafPriority
end ThreeUniformDiaries
