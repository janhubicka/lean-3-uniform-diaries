import ThreeUniformDiaries.DiaryFullRoleDefinition

/-!
# Track A: a genuinely FINITE E2/E3/E5 induced-edge gate

For a map on a FINITE supported set S containing the three markers,
assume strict order preservation, exact preservation of the three
nonmarker roles, and exact S1 singleton-meet transport for any pair
of supported genuine leaves (with its source meet also in S).

Then the induced edge AND nonedge table on S is exactly equivalent
to its restrictions to the E2, E3, and E5 permitted-edge shapes.
E1 marker-role bits follow from role preservation. E4 Devlin marker
pair bits follow from the right E2 branch at the S1 singleton meet.
Target permitted-edge classification and reflected roles are used
to prove the nonedge direction, not merely preservation of edges.

The E5 family is independent in this FINITE lemma because the
hypotheses do not already assume inducedness on the leaf reduct.
No candidate existence, S2 table, future order reserve, or
countable diary-unavoidability theorem follows here.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Finite, two-sided inducedness is equivalent to E2, E3, E5 tests.
Every source vertex in every test must lie in the chosen finite
set S; freshly generated split vertices below old leaves are
therefore included, not silently ignored. -/
theorem RoleDiary.finite_induced_iff_E2_E3_E5
    {H K : Ordered3Graph Nat}
    (DH : RoleDiary H) (DK : RoleDiary K)
    (S : Finset Nat) (f : Nat → Nat)
    (h0S : 0 ∈ S) (h1S : 1 ∈ S) (h2S : 2 ∈ S)
    (h0 : f 0 = 0) (h1 : f 1 = 1) (h2 : f 2 = 2)
    (hOrder : ∀ a b : Nat, a ∈ S → b ∈ S → a < b → f a < f b)
    (hLeafRole : ∀ a : Nat, a ∈ S → IsLeaf H a → IsLeaf K (f a))
    (hOneRole : ∀ a : Nat, a ∈ S → IsOneSplit H a → IsOneSplit K (f a))
    (hTwoRole : ∀ a : Nat, a ∈ S → IsTwoSplit H a → IsTwoSplit K (f a))
    (hOneMeet : ∀ a b : Nat,
      a ∈ S → b ∈ S → a < b →
      IsLeaf H a → IsLeaf H b →
      H.oneMeetLevel a b ∈ S ∧
      K.oneMeetLevel (f a) (f b) = f (H.oneMeetLevel a b)) :
    (∀ a b c : Nat, a ∈ S → b ∈ S → c ∈ S →
      a < b → b < c →
      (H.edge a b c ↔ K.edge (f a) (f b) (f c))) ↔
    ((∀ s b : Nat, s ∈ S → b ∈ S →
        IsOneSplit H s → IsLeaf H b → s < b →
        (H.edge 0 s b ↔ K.edge 0 (f s) (f b))) ∧
     (∀ s a b : Nat, s ∈ S → a ∈ S → b ∈ S →
        IsTwoSplit H s → IsLeaf H a → IsLeaf H b →
        s < a → a < b →
        (H.edge s a b ↔ K.edge (f s) (f a) (f b))) ∧
     (∀ a b c : Nat, a ∈ S → b ∈ S → c ∈ S →
        IsLeaf H a → IsLeaf H b → IsLeaf H c →
        a < b → b < c →
        (H.edge a b c ↔ K.edge (f a) (f b) (f c)))) := by
  classical
  constructor
  · intro hInduced
    refine ⟨?_, ?_, ?_⟩
    · intro s b hsS hbS hs hb hsb
      have h0s : 0 < s := by omega
      simpa only [h0] using hInduced 0 s b h0S hsS hbS h0s hsb
    · intro s a b hsS haS hbS hs ha hb hsa hab
      exact hInduced s a b hsS haS hbS hsa hab
    · intro a b c haS hbS hcS ha hb hc hab hbc
      exact hInduced a b c haS hbS hcS hab hbc
  · rintro ⟨hE2, hE3, hE5⟩
    have hMarker0 (x : Nat) (hx : x ∈ S)
        (hx0 : f x = 0) : x = 0 := by
      by_contra hne
      have hxpos : 0 < x := by omega
      have hlt := hOrder 0 x h0S hx hxpos
      rw [h0, hx0] at hlt
      omega
    have hMarker1 (x : Nat) (hx : x ∈ S)
        (hx1 : f x = 1) : x = 1 := by
      rcases lt_trichotomy x 1 with hlt | heq | hgt
      · have hImage := hOrder x 1 hx h1S hlt
        rw [hx1, h1] at hImage
        omega
      · exact heq
      · have hImage := hOrder 1 x h1S hx hgt
        rw [hx1, h1] at hImage
        omega
    have hMarker2 (x : Nat) (hx : x ∈ S)
        (hx2 : f x = 2) : x = 2 := by
      rcases lt_trichotomy x 2 with hlt | heq | hgt
      · have hImage := hOrder x 2 hx h2S hlt
        rw [hx2, h2] at hImage
        omega
      · exact heq
      · have hImage := hOrder 2 x h2S hx hgt
        rw [hx2, h2] at hImage
        omega
    have hNonmarker (x : Nat) (hx : x ∈ S)
        (hfx : 3 ≤ f x) : 3 ≤ x := by
      by_contra hnot
      have hxle : x ≤ 2 := by omega
      have hImage : f x ≤ f 2 := by
        rcases lt_or_eq_of_le hxle with hlt | heq
        · exact (hOrder x 2 hx h2S hlt).le
        · rw [heq]
      rw [h2] at hImage
      omega
    have hLeafRefl (x : Nat) (hx : x ∈ S)
        (hTarget : IsLeaf K (f x)) : IsLeaf H x := by
      have hx3 : 3 ≤ x := hNonmarker x hx hTarget.1
      rcases DH.role_valid x hx3 with hLeaf | hOne | hTwo
      · exact hLeaf
      · have hTargetOne := hOneRole x hx hOne
        exact False.elim (hTarget.2.1 hTargetOne.2.1)
      · have hTargetTwo := hTwoRole x hx hTwo
        exact False.elim (hTarget.2.2 hTargetTwo.2.2)
    have hOneRefl (x : Nat) (hx : x ∈ S)
        (hTarget : IsOneSplit K (f x)) : IsOneSplit H x := by
      have hx3 : 3 ≤ x := hNonmarker x hx hTarget.1
      rcases DH.role_valid x hx3 with hLeaf | hOne | hTwo
      · have hTargetLeaf := hLeafRole x hx hLeaf
        exact False.elim (hTargetLeaf.2.1 hTarget.2.1)
      · exact hOne
      · have hTargetTwo := hTwoRole x hx hTwo
        exact False.elim (hTarget.2.2 hTargetTwo.2.2)
    have hTwoRefl (x : Nat) (hx : x ∈ S)
        (hTarget : IsTwoSplit K (f x)) : IsTwoSplit H x := by
      have hx3 : 3 ≤ x := hNonmarker x hx hTarget.1
      rcases DH.role_valid x hx3 with hLeaf | hOne | hTwo
      · have hTargetLeaf := hLeafRole x hx hLeaf
        exact False.elim (hTargetLeaf.2.2 hTarget.2.2)
      · have hTargetOne := hOneRole x hx hOne
        exact False.elim (hTargetOne.2.2 hTarget.2.2)
      · exact hTwo
    have hE1 (z : Nat) (hzS : z ∈ S) (hz3 : 3 ≤ z) :
        (H.edge 0 1 z ↔ K.edge 0 1 (f z)) ∧
        (H.edge 0 2 z ↔ K.edge 0 2 (f z)) := by
      rcases DH.role_valid z hz3 with hLeaf | hOne | hTwo
      · have ht := hLeafRole z hzS hLeaf
        exact ⟨iff_of_false hLeaf.2.1 ht.2.1,
          iff_of_false hLeaf.2.2 ht.2.2⟩
      · have ht := hOneRole z hzS hOne
        exact ⟨iff_of_true hOne.2.1 ht.2.1,
          iff_of_false hOne.2.2 ht.2.2⟩
      · have ht := hTwoRole z hzS hTwo
        exact ⟨iff_of_false hTwo.2.1 ht.2.1,
          iff_of_true hTwo.2.2 ht.2.2⟩
    have hE4 (a b : Nat) (haS : a ∈ S) (hbS : b ∈ S)
        (hab : a < b) (ha : IsLeaf H a) (hb : IsLeaf H b) :
        (H.edge 1 a b ↔ K.edge 1 (f a) (f b)) ∧
        (H.edge 2 a b ↔ K.edge 2 (f a) (f b)) := by
      let s := H.oneMeetLevel a b
      have hsRole : IsOneSplit H s :=
        DH.singleton_meets a b ha hb (ne_of_lt hab)
      obtain ⟨hsS, hExact⟩ := hOneMeet a b haS hbS hab ha hb
      have hsCap : s ≤ a :=
        (H.oneMeetLevel_le_min a b).trans (min_le_left _ _)
      have hsNe : s ≠ a := by
        intro hsEq
        have hsOneA : IsOneSplit H a := by
          simpa only [hsEq] using hsRole
        exact ha.2.1 hsOneA.2.1
      have hsa : s < a := by omega
      have hsb : s < b := by omega
      have hTa : IsLeaf K (f a) := hLeafRole a haS ha
      have hTb : IsLeaf K (f b) := hLeafRole b hbS hb
      have hTs : IsOneSplit K (f s) := hOneRole s hsS hsRole
      have hSourceLex :
          LexEarlier H a b ↔ H.edge 0 s b :=
        DH.lexEarlier_iff_right_split_marker s a b
          hsRole ha hb hab hsa rfl
      have hTargetLex :
          LexEarlier K (f a) (f b) ↔ K.edge 0 (f s) (f b) :=
        DK.lexEarlier_iff_right_split_marker (f s) (f a) (f b)
          hTs hTa hTb (hOrder a b haS hbS hab)
          (hOrder s a hsS haS hsa) hExact
      have hLex :
          LexEarlier H a b ↔ LexEarlier K (f a) (f b) :=
        hSourceLex.trans
          ((hE2 s b hsS hbS hsRole hb hsb).trans hTargetLex.symm)
      constructor
      · exact (DH.leaf_marker_one a b hab ha hb).trans
          (hLex.trans
            (DK.leaf_marker_one (f a) (f b)
              (hOrder a b haS hbS hab) hTa hTb).symm)
      · exact (DH.leaf_marker_two a b hab ha hb).trans
          ((not_congr hLex).trans
            (DK.leaf_marker_two (f a) (f b)
              (hOrder a b haS hbS hab) hTa hTb).symm)
    have hShape (a b c : Nat) (haS : a ∈ S) (hbS : b ∈ S)
        (hcS : c ∈ S) (hab : a < b) (hbc : b < c)
        (hAllowed : PermittedDiaryEdge H a b c) :
        H.edge a b c ↔ K.edge (f a) (f b) (f c) := by
      rcases hAllowed with hrole | hsplit | htwo | hdevlin | hnormal
      · rcases hrole with ⟨ha0, hb, hc3⟩
        rcases hb with hb1 | hb2
        · subst a
          subst b
          simpa only [h0, h1] using (hE1 c hcS hc3).1
        · subst a
          subst b
          simpa only [h0, h2] using (hE1 c hcS hc3).2
      · rcases hsplit with ⟨ha0, hbOne, hcLeaf⟩
        subst a
        simpa only [h0] using
          (hE2 b c hbS hcS hbOne hcLeaf hbc)
      · rcases htwo with ⟨haTwo, hbLeaf, hcLeaf⟩
        exact hE3 a b c haS hbS hcS haTwo hbLeaf hcLeaf hab hbc
      · rcases hdevlin with ⟨haMarker, hbLeaf, hcLeaf⟩
        rcases haMarker with ha1 | ha2
        · subst a
          simpa only [h1] using
            (hE4 b c hbS hcS hbc hbLeaf hcLeaf).1
        · subst a
          simpa only [h2] using
            (hE4 b c hbS hcS hbc hbLeaf hcLeaf).2
      · rcases hnormal with ⟨haLeaf, hbLeaf, hcLeaf⟩
        exact hE5 a b c haS hbS hcS haLeaf hbLeaf hcLeaf hab hbc
    have hReflectPermitted (a b c : Nat)
        (haS : a ∈ S) (hbS : b ∈ S) (hcS : c ∈ S)
        (hK : K.edge (f a) (f b) (f c)) :
        PermittedDiaryEdge H a b c := by
      rcases DK.permitted_edge (f a) (f b) (f c) hK with
        hrole | hsplit | htwo | hdevlin | hnormal
      · rcases hrole with ⟨ha0, hb, hc3⟩
        have hbMarker : b = 1 ∨ b = 2 := by
          rcases hb with hb1 | hb2
          · exact Or.inl (hMarker1 b hbS hb1)
          · exact Or.inr (hMarker2 b hbS hb2)
        exact Or.inl
          ⟨hMarker0 a haS ha0, hbMarker, hNonmarker c hcS hc3⟩
      · rcases hsplit with ⟨ha0, hbOne, hcLeaf⟩
        exact Or.inr (Or.inl
          ⟨hMarker0 a haS ha0,
           hOneRefl b hbS hbOne, hLeafRefl c hcS hcLeaf⟩)
      · rcases htwo with ⟨haTwo, hbLeaf, hcLeaf⟩
        exact Or.inr (Or.inr (Or.inl
          ⟨hTwoRefl a haS haTwo,
           hLeafRefl b hbS hbLeaf, hLeafRefl c hcS hcLeaf⟩))
      · rcases hdevlin with ⟨haMarker, hbLeaf, hcLeaf⟩
        have haTag : a = 1 ∨ a = 2 := by
          rcases haMarker with ha1 | ha2
          · exact Or.inl (hMarker1 a haS ha1)
          · exact Or.inr (hMarker2 a haS ha2)
        exact Or.inr (Or.inr (Or.inr (Or.inl
          ⟨haTag, hLeafRefl b hbS hbLeaf, hLeafRefl c hcS hcLeaf⟩)))
      · rcases hnormal with ⟨haLeaf, hbLeaf, hcLeaf⟩
        exact Or.inr (Or.inr (Or.inr (Or.inr
          ⟨hLeafRefl a haS haLeaf,
           hLeafRefl b hbS hbLeaf, hLeafRefl c hcS hcLeaf⟩)))
    intro a b c haS hbS hcS hab hbc
    constructor
    · intro hH
      exact (hShape a b c haS hbS hcS hab hbc
        (DH.permitted_edge a b c hH)).mp hH
    · intro hK
      exact (hShape a b c haS hbS hcS hab hbc
        (hReflectPermitted a b c haS hbS hcS hK)).mpr hK

end DiaryLeafPriority
end ThreeUniformDiaries
