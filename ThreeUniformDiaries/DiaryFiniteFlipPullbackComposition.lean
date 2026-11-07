import ThreeUniformDiaries.DiaryFiniteFlipAbsorptionUpwardClosure

/-!
# Track B: functorial exact pullback of genuine finite target flips

For a bounded protected embedding f:A -> B and an arbitrary map g,
the canonical pulled-back edge table on the bounded source interval
satisfies the literal composition identity:

  Pullback (Pullback T m g) n f = Pullback T n (g ∘ f).

The intermediate pullback contains extra increasing-triple/frame
guards. The guards are exactly discharged by f's strict monotonicity
and image bound. Thus this identity is non-vacuous: the full edge
and NONEDGE tables match, not just the leaf reduct.

When B -> C is itself a bounded protected embedding and T is an
actual genuine finite flip of C, both iterated and directly pulled
back graphs are genuine finite flips of A, literally the same graph.
This makes the *target flip pullback data* coherent under protected
finite tower embeddings.

It DOES NOT prove that independently chosen source A-copies in the
flipped targets are coherent, or construct a countable full diary
carrier, or establish the unrestricted countable-source flip
property.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- EXACT equality of all ordered edge/nonedge tables when canonical
bounded pullbacks are composed along a true bounded meet embedding.
No target flip assumptions are needed for this purely relational
identity; they are needed only to know the pullbacks are diaries. -/
theorem finiteDiaryPullbackGraph_comp_of_bounded
    {A B T : Ordered3Graph Nat} {n m : Nat}
    {f : Nat → Nat}
    (E : FiniteBoundedMeetEmbedding A B n m f)
    (g : Nat → Nat) :
    finiteDiaryPullbackGraph
      (finiteDiaryPullbackGraph T m g) n f =
    finiteDiaryPullbackGraph T n (fun u => g (f u)) := by
  apply finiteDiary_graph_ext
  intro a b c
  constructor
  · intro h
    obtain ⟨hab,hbc,hcn,hInner⟩ := h
    exact ⟨hab,hbc,hcn,hInner.2.2.2⟩
  · intro h
    obtain ⟨hab,hbc,hcn,hEdge⟩ := h
    have hAB : f a < f b := E.toMeetEmbedding.strictMono hab
    have hBC : f b < f c := E.toMeetEmbedding.strictMono hbc
    have hC : f c < m := E.image_bound c hcn
    exact ⟨hab,hbc,hcn,⟨hAB,hBC,hC,hEdge⟩⟩

/-- True flip data along two nested bounded protected copies
pull back to the same exact source finite diary as the single
composite copy. Both intermediate and final pullbacks are genuine
finite full diaries and genuine identity-on-vertices source flips.

In particular, the flip restriction maps along any finite target
tower satisfy strict associativity at the FULL EDGE-TABLE level. -/
theorem finiteDiaryPullbackGraph_comp_sourceFlip
    {A B C T : Ordered3Graph Nat} {n m l : Nat}
    {f g : Nat → Nat}
    (DA : FiniteRoleDiaryBlock A n)
    (DB : FiniteRoleDiaryBlock B m)
    (E : FiniteBoundedMeetEmbedding A B n m f)
    (D : FiniteBoundedMeetEmbedding B C m l g)
    (FT : FiniteDiaryFlip C T l) :
    FiniteDiaryFlip B (finiteDiaryPullbackGraph T m g) m ∧
      FiniteDiaryFlip A
        (finiteDiaryPullbackGraph T n (fun u => g (f u))) n ∧
      finiteDiaryPullbackGraph
        (finiteDiaryPullbackGraph T m g) n f =
      finiteDiaryPullbackGraph T n (fun u => g (f u)) := by
  have FB : FiniteDiaryFlip B (finiteDiaryPullbackGraph T m g) m :=
    finiteDiaryPullbackGraph_is_sourceFlip
      DB D.toMeetEmbedding D.image_bound FT
  have FAraw : FiniteDiaryFlip A
      (finiteDiaryPullbackGraph
        (finiteDiaryPullbackGraph T m g) n f) n :=
    finiteDiaryPullbackGraph_is_sourceFlip
      DA E.toMeetEmbedding E.image_bound FB
  have hEq :
      finiteDiaryPullbackGraph
        (finiteDiaryPullbackGraph T m g) n f =
      finiteDiaryPullbackGraph T n (fun u => g (f u)) :=
    finiteDiaryPullbackGraph_comp_of_bounded (T := T) E g
  refine ⟨FB, ?_, hEq⟩
  rw [hEq] at FAraw
  exact FAraw

end DiaryLeafPriority
end ThreeUniformDiaries
