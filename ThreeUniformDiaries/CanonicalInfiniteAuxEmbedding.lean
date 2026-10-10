import ThreeUniformDiaries.CanonicalInfiniteExactMeets
import ThreeUniformDiaries.FiniteExactMeetInterface

/-!
# The selected-level map into the countable canonical image is
# genuinely auxiliary-type-respecting

The coherent infinite image graph is not just an induced copy of
the source hypergraph. Its exact singleton and auxiliary capped
meet levels are the images of the corresponding source meets.
Therefore the selected-level vertex map defines a fully
aux-type-respecting embedding, with preservation AND reflection
of all equality-of-type tests at their corresponding cuts.

This verifies the substantive infinite branch component of the
manuscript's Lemma auxtypeemb in the actual Ordered3Graph language.
The remaining identification with F_I on the relative branch
carrier and with an actual strong vector subtree is separate.
-/

namespace ThreeUniformDiaries
namespace CanonicalMap

/-- Every algebraic canonical map yields an actual induced
embedding of any countable enumerated hypergraph into its
coherently constructed countable image hypergraph. -/
noncomputable def imageGraph_embedding
    (F : CanonicalMap) (H : Ordered3Graph Nat) :
    Ordered3Graph.Embedding H (F.imageGraph H) where
  toFun := F.level
  strictMono := F.strictMono
  edge_iff := by
    intro a b c hab hbc
    exact (F.imageGraph_selected_edges H hab hbc).symm

/-- The resulting embedding preserves and reflects all source
singleton/auxiliary type equalities, including missing ambient
target indices, by the exact capped-meet theorems. -/
theorem imageGraph_auxTypeRespecting
    (F : CanonicalMap) (H : Ordered3Graph Nat) :
    (F.imageGraph_embedding H).AuxTypeRespecting := by
  constructor
  · intro l u v hlu hlv
    change H.SameOneTypeBelow l u v ↔
      (F.imageGraph H).SameOneTypeBelow
        (F.level l) (F.level u) (F.level v)
    have hcap : l ≤ min u v := le_min hlu hlv
    have hcapF :
        F.level l ≤ min (F.level u) (F.level v) :=
      le_min (F.strictMono.monotone hlu) (F.strictMono.monotone hlv)
    rw [H.sameOneTypeBelow_iff_le_oneMeetLevel l u v hcap,
      (F.imageGraph H).sameOneTypeBelow_iff_le_oneMeetLevel
        (F.level l) (F.level u) (F.level v) hcapF,
      F.imageGraph_oneMeetLevel_preserved H u v]
    constructor
    · intro h
      exact F.strictMono.monotone h
    · intro h
      by_contra hnot
      have hlt : H.oneMeetLevel u v < l :=
        Nat.lt_of_not_ge hnot
      exact (not_le_of_gt (F.strictMono hlt)) h
  · intro l u₀ u₁ v₀ v₁ hlu hu hlv hv
    change H.SameAuxTypeBelow l u₀ u₁ v₀ v₁ ↔
      (F.imageGraph H).SameAuxTypeBelow
        (F.level l) (F.level u₀) (F.level u₁)
        (F.level v₀) (F.level v₁)
    have hcap : l ≤ min u₀ v₀ := le_min hlu hlv
    have hcapF :
        F.level l ≤ min (F.level u₀) (F.level v₀) :=
      le_min (F.strictMono.monotone hlu) (F.strictMono.monotone hlv)
    rw [H.sameAuxTypeBelow_iff_le_auxMeetLevel
        l u₀ u₁ v₀ v₁ hcap,
      (F.imageGraph H).sameAuxTypeBelow_iff_le_auxMeetLevel
        (F.level l) (F.level u₀) (F.level u₁)
        (F.level v₀) (F.level v₁) hcapF,
      F.imageGraph_auxMeetLevel_preserved H u₀ u₁ v₀ v₁ hu hv]
    constructor
    · intro h
      exact F.strictMono.monotone h
    · intro h
      by_contra hnot
      have hlt : H.auxMeetLevel u₀ u₁ v₀ v₁ < l :=
        Nat.lt_of_not_ge hnot
      exact (not_le_of_gt (F.strictMono hlt)) h

end CanonicalMap
end ThreeUniformDiaries
