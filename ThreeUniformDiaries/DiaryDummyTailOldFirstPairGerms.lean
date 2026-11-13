import ThreeUniformDiaries.DiaryDummyTailUniformOldGerms
import ThreeUniformDiaries.DiaryOnePassCodeEquivalence
import Lean.Elab.Tactic.Omega

/-!
# Track B: old-first, new-second leaf pairs share one global old-cut germ

The concrete dummy-leaf tail has OLD-to-tail marker incidences that
are independent of WHICH tail leaf is chosen. For a fixed old first
coordinate a<n, any two ordered pairs (a,z), (a,z') with z,z'>=n
therefore have the SAME complete two-type at every cut m<=n.

The first-coordinate singleton code is literally identical, the
second-coordinate singleton codes of the tail leaves are identical,
and all auxiliary edges (x,a,z)/(x,a,z') are copied through the
same old-middle/tail marker formula.

At old m<n with m<=a, the actual ordered-pair germ signatures
are therefore identical as well, including the special TERMINAL
case a=m where their child code is none. Thus each OLD first
coordinate contributes at most ONE cross-tail pair germ at every
protected old cut.

Together with the already checked homogeneous pure-tail pair germs,
this is the key step toward an exact FINITE census of globally
realised dummy-tail germ types. It does not prove the required
old-tail germ is compatible with existing OLD pair germs, which
remains a substantive protected-relative-extension issue.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- Fix an old first vertex a<n. Changing the second
coordinate among arbitrary dummy-tail leaves does not change
the FULL ordered-pair type below any old cut m<=n. -/
theorem finiteDummyTail_oldFirst_tailSecond_twoTypeBelow_oldCut
    (H : Ordered3Graph Nat) (n : Nat) (bits : Nat → Bool)
    (m a z z' : Nat)
    (hm : m ≤ n) (ha : a < n)
    (hz : n ≤ z) (hz' : n ≤ z') :
    (finiteDummyTailCarrier H n bits).SameTwoTypeBelow
      m a z a z' := by
  refine ⟨?_,?_,?_⟩
  · intro x y _hxy _hym
    rfl
  · exact finiteDummyTail_allTail_oneTypeBelow_oldCut
      H n bits m z z' hm hz hz'
  · intro x _hx
    exact (finiteDummyTail_oldMiddle_tailEdge_iff
      H n bits x a z ha hz).trans
        (finiteDummyTail_oldMiddle_tailEdge_iff
          H n bits x a z' ha hz').symm

/-- All actual old-first/tail-second ordered pairs with a FIXED
old first coordinate have the same full pair-germ child at each
old m<n, whether m=a (terminal germ) or m<a (normal germ). -/
theorem finiteDummyTail_oldFirst_tailSecond_twoGermCode_eq
    (H : Ordered3Graph Nat) (n : Nat) (bits : Nat → Bool)
    (m a z z' : Nat)
    (hm : m < n) (hma : m ≤ a) (ha : a < n)
    (hz : n ≤ z) (hz' : n ≤ z') :
    twoGermCode (finiteDummyTailCarrier H n bits) m a z =
      twoGermCode (finiteDummyTailCarrier H n bits) m a z' := by
  let T : Ordered3Graph Nat := finiteDummyTailCarrier H n bits
  by_cases hTerm : a = m
  · subst a
    have hCode : twoCode T m m z = twoCode T m m z' := by
      apply (twoCode_eq_iff_sameTwoType T m m z m z').mpr
      exact finiteDummyTail_oldFirst_tailSecond_twoTypeBelow_oldCut
        H n bits m m z z' (by omega) (by omega) hz hz'
    simp only [twoGermCode, if_pos rfl]
    exact congrArg (fun c : TwoCodeSpace m =>
      (c, (none : Option (TwoCodeSpace (m+1))))) hCode
  · apply (twoGerm_eq_iff_normal T m a z a z' hTerm hTerm).mpr
    constructor
    · exact finiteDummyTail_oldFirst_tailSecond_twoTypeBelow_oldCut
        H n bits m a z z' (by omega) ha hz hz'
    · exact finiteDummyTail_oldFirst_tailSecond_twoTypeBelow_oldCut
        H n bits (m+1) a z z' (by omega) ha hz hz'

end DiaryLeafPriority
end ThreeUniformDiaries
