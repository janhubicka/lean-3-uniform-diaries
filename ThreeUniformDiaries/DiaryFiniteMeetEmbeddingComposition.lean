import ThreeUniformDiaries.DiaryFiniteMeetEmbedding

/-!
# Composition of induced finite numerical-meet embeddings

Iterated finite ordered sums must not forget older input copies.
The finite embedding interface fixes marker levels 0,1,2,
reflects ordered ternary edges AND nonedges, reflects the literal
marker-defined roles, and preserves all capped numerical
singleton and full pair-type meets on nonmarker source vertices.

We prove closure under composition when the first embedding's
entire nonmarker finite range lies inside the second embedding's
finite domain. The second domain has at least three vertices,
ensuring the first embedding's markers also lie in its range.

No source/target global RoleDiary on the artificial Nat tails.
This is the reusable bookkeeping for arbitrary finite families.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

variable {H T U : Ordered3Graph Nat}
variable {n m : Nat} {f g : Nat → Nat}

/-- Finite induced meet embeddings compose, provided all bounded
nonmarker vertices of the source have images in the next finite
domain. The true induced reflection, role reflection, and both
numerical meet equations are preserved. -/
theorem FiniteMeetEmbedding.comp
    (E : FiniteMeetEmbedding H T n f)
    (D : FiniteMeetEmbedding T U m g)
    (hm : 3 ≤ m)
    (hRange : ∀ u : Nat, 3 ≤ u → u < n → f u < m) :
    FiniteMeetEmbedding H U n (fun x => g (f x)) := by
  have hDom : ∀ u : Nat, 3 ≤ u → u < n →
      3 ≤ f u ∧ f u < m := by
    intro u hu3 hun
    have h2u : 2 < u := by omega
    have hfu := E.strictMono h2u
    rw [E.marker_two] at hfu
    exact ⟨by omega, hRange u hu3 hun⟩
  have hFinite : ∀ u : Nat, u < n → f u < m := by
    intro u hun
    by_cases hu3 : 3 ≤ u
    · exact hRange u hu3 hun
    · have hlt : u < 3 := by omega
      have hCases : u = 0 ∨ u = 1 ∨ u = 2 := by omega
      rcases hCases with h0 | h1 | h2
      · subst u
        rw [E.marker_zero]
        omega
      · subst u
        rw [E.marker_one]
        omega
      · subst u
        rw [E.marker_two]
        omega
  refine {
    strictMono := ?_
    marker_zero := ?_
    marker_one := ?_
    marker_two := ?_
    edge_iff := ?_
    leaf_iff := ?_
    oneSplit_iff := ?_
    twoSplit_iff := ?_
    oneMeet := ?_
    twoMeet := ?_
  }
  · intro a b hab
    exact D.strictMono (E.strictMono hab)
  · change g (f 0) = 0
    rw [E.marker_zero, D.marker_zero]
  · change g (f 1) = 1
    rw [E.marker_one, D.marker_one]
  · change g (f 2) = 2
    rw [E.marker_two, D.marker_two]
  · intro a b c hab hbc hcn
    change (U.edge (g (f a)) (g (f b)) (g (f c)) ↔ H.edge a b c)
    exact (D.edge_iff (f a) (f b) (f c)
      (E.strictMono hab) (E.strictMono hbc) (hFinite c hcn)).trans
      (E.edge_iff a b c hab hbc hcn)
  · intro u hu3 hun
    change IsLeaf U (g (f u)) ↔ IsLeaf H u
    have hd := hDom u hu3 hun
    exact (D.leaf_iff (f u) hd.1 hd.2).trans
      (E.leaf_iff u hu3 hun)
  · intro u hu3 hun
    change IsOneSplit U (g (f u)) ↔ IsOneSplit H u
    have hd := hDom u hu3 hun
    exact (D.oneSplit_iff (f u) hd.1 hd.2).trans
      (E.oneSplit_iff u hu3 hun)
  · intro u hu3 hun
    change IsTwoSplit U (g (f u)) ↔ IsTwoSplit H u
    have hd := hDom u hu3 hun
    exact (D.twoSplit_iff (f u) hd.1 hd.2).trans
      (E.twoSplit_iff u hu3 hun)
  · intro u v hu3 hun hv3 hvn
    have hdu := hDom u hu3 hun
    have hdv := hDom v hv3 hvn
    change U.oneMeetLevel (g (f u)) (g (f v)) =
      g (f (H.oneMeetLevel u v))
    calc
      U.oneMeetLevel (g (f u)) (g (f v)) =
          g (T.oneMeetLevel (f u) (f v)) :=
        D.oneMeet (f u) (f v)
          hdu.1 hdu.2 hdv.1 hdv.2
      _ = g (f (H.oneMeetLevel u v)) := by
        rw [E.oneMeet u v hu3 hun hv3 hvn]
  · intro a b c d hab hcd ha3 han hb3 hbn hc3 hcn hd3 hdn
    have hda := hDom a ha3 han
    have hdb := hDom b hb3 hbn
    have hdc := hDom c hc3 hcn
    have hdd := hDom d hd3 hdn
    change U.twoMeetLevel (g (f a)) (g (f b))
      (g (f c)) (g (f d)) =
      g (f (H.twoMeetLevel a b c d))
    calc
      U.twoMeetLevel (g (f a)) (g (f b))
          (g (f c)) (g (f d)) =
          g (T.twoMeetLevel (f a) (f b)
            (f c) (f d)) :=
        D.twoMeet (f a) (f b) (f c) (f d)
          (E.strictMono hab) (E.strictMono hcd)
          hda.1 hda.2 hdb.1 hdb.2
          hdc.1 hdc.2 hdd.1 hdd.2
      _ = g (f (H.twoMeetLevel a b c d)) := by
        rw [E.twoMeet a b c d hab hcd
          ha3 han hb3 hbn hc3 hcn hd3 hdn]

end DiaryLeafPriority
end ThreeUniformDiaries
