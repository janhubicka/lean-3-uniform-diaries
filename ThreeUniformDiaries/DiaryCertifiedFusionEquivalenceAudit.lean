import ThreeUniformDiaries.DiaryCountableCertifiedFusion

/-!
# Adversarial audit: unrestricted "safe stage" certificates are equivalent
  to supplying a coherent countable family

A certified-stage fusion system produces a coherent countable family
(PR #964). The converse is ALSO true, with no new mathematics:
if a coherent family already exists, declare Safe m f to mean
literally f = P.map m. Every such safe map has the next selected
map as a compatible successor. We formalise this converse and the
if-and-only-if.

Thus existentially postulating an ARBITRARY Safe predicate is just
a repackaging of the open countable-source unavoidability problem.
A useful future theorem must construct a *specified* local/geometric
Safe predicate with independently provable extension, not select Safe
after assuming the sought infinite embedding.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

namespace CoherentCofinalDiarySupportMaps

variable {H K : Ordered3Graph Nat} {DH : RoleDiary H} {F : Nat → Nat}

/-- The stage map of an already supplied coherent family is admissible,
provided its genuine leaves are in the stated range. -/
theorem stage_admissible
    (P : CoherentCofinalDiarySupportMaps DH K)
    (hRange : ∀ m u : Nat,
      u ∈ countableDiaryFiniteSupport H m →
      IsLeaf H u → ∃ t : Nat, P.map m u = F t)
    (m : Nat) :
    AdmissibleCofinalDiaryStage H K F m (P.map m) := by
  refine {
    ordered := ?_
    marker_zero := P.marker_zero m
    marker_one := P.marker_one m
    marker_two := P.marker_two m
    leaf_role := ?_
    one_split_role := ?_
    two_split_role := ?_
    induced_edge := ?_
    leaf_oneMeet := ?_
    leaf_twoMeet := ?_
    leaf_range := ?_
  }
  · intro u v hu hv huv
    exact P.ordered m u v hu hv huv
  · intro u hu hLeaf
    exact P.leaf_role m u hu hLeaf
  · intro u hu hOne
    exact P.one_split_role m u hu hOne
  · intro u hu hTwo
    exact P.two_split_role m u hu hTwo
  · intro a b c ha hb hc hab hbc
    exact P.induced_edge m a b c ha hb hc hab hbc
  · intro a b ha hb hLa hLb
    exact P.leaf_oneMeet m a b ha hb hLa hLb
  · intro a b c d ha hb hc hd hab hcd hLa hLb hLc hLd
    exact P.leaf_twoMeet m a b c d ha hb hc hd hab hcd hLa hLb hLc hLd
  · intro u hu hLeaf
    exact hRange m u hu hLeaf

/-- A completely unrestricted Safe predicate can always be
manufactured FROM an already-existing coherent family. -/
def toCertified
    (P : CoherentCofinalDiarySupportMaps DH K)
    (hRange : ∀ m u : Nat,
      u ∈ countableDiaryFiniteSupport H m →
      IsLeaf H u → ∃ t : Nat, P.map m u = F t) :
    CertifiedDiaryFusionData DH K F where
  Safe := fun m f => f = P.map m
  valid := by
    intro m f hf
    subst f
    exact P.stage_admissible hRange m
  initial := ⟨P.map 0, rfl⟩
  next := by
    intro m f hf
    refine ⟨P.map (m + 1), rfl, ?_⟩
    intro u hu
    subst f
    exact (P.coherent m (m + 1) (by omega) u hu).symm

end CoherentCofinalDiarySupportMaps

/-- The existential "safe-stage fusion certificate" hypothesis is
exactly equivalent to the existence of a coherent countable family,
so by itself it is not an independent route to unavoidability. -/
theorem certifiedDiaryFusion_iff_coherent
    {H K : Ordered3Graph Nat} (DH : RoleDiary H) (F : Nat → Nat) :
    Nonempty (CertifiedDiaryFusionData DH K F) ↔
      ∃ P : CoherentCofinalDiarySupportMaps DH K,
        ∀ m u : Nat,
          u ∈ countableDiaryFiniteSupport H m →
          IsLeaf H u → ∃ t : Nat, P.map m u = F t := by
  constructor
  · rintro ⟨C⟩
    exact C.exists_coherent
  · rintro ⟨P,hRange⟩
    exact ⟨P.toCertified hRange⟩

end DiaryLeafPriority
end ThreeUniformDiaries
