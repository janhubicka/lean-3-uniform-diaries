import ThreeUniformDiaries.DiaryTailSingletonTypeCone

/-!
# Complete old-cut singleton types are finite edge-bit codes

For any numerical cut B, the full mixed singleton type of a target
leaf v below B is represented exactly by its finite subset of the
increasing test pairs x<y<B for which K.edge x y v holds.

Two vertices have identical codes iff their genuine
SameOneTypeBelow B predicate holds. Thus "same mixed tail cone"
is a finite colouring of the target leaf set, not an abstract
infinite type restriction, and every code is drawn from the
finite powerset of the pairs below B.

The exact code does NOT show that any prescribed U->leaves(K)
copy has enough members of a particular cone, nor any persistent
relative diary extension. It only supplies the correct finite
interface for a future type-refinement/Ramsey argument.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- All increasing ordered pairs of numerical testing positions
strictly below the finite cut B. -/
noncomputable def tailOneTypeTests (B : Nat) : Finset (Nat × Nat) := by
  classical
  exact ((Finset.range B).product (Finset.range B)).filter
    (fun p => p.1 < p.2)

theorem mem_tailOneTypeTests_iff (B x y : Nat) :
    (x,y) ∈ tailOneTypeTests B ↔ x < y ∧ y < B := by
  classical
  constructor
  · intro h
    change (x,y) ∈
      ((Finset.range B).product (Finset.range B)).filter
        (fun p => p.1 < p.2) at h
    obtain ⟨hp,hxy⟩ := Finset.mem_filter.mp h
    have hyB := (Finset.mem_product.mp hp).2
    exact ⟨hxy,Finset.mem_range.mp hyB⟩
  · rintro ⟨hxy,hyB⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega),
       Finset.mem_range.mpr hyB⟩,hxy⟩

/-- The finite set of tests with positive edge bit to v. -/
noncomputable def tailOneTypeCode
    (K : Ordered3Graph Nat) (B v : Nat) : Finset (Nat × Nat) := by
  classical
  exact (tailOneTypeTests B).filter (fun p => K.edge p.1 p.2 v)

theorem mem_tailOneTypeCode_iff
    (K : Ordered3Graph Nat) (B x y v : Nat) :
    (x,y) ∈ tailOneTypeCode K B v ↔
      x < y ∧ y < B ∧ K.edge x y v := by
  classical
  rw [tailOneTypeCode,Finset.mem_filter,
    mem_tailOneTypeTests_iff B x y]
  
/-- Equality of finite edge-bit tables is equivalent to equality of
the entire (mixed) singleton type below B, including nonedges. -/
theorem tailOneTypeCode_eq_iff_sameOneTypeBelow
    (K : Ordered3Graph Nat) (B u v : Nat) :
    tailOneTypeCode K B u = tailOneTypeCode K B v ↔
      K.SameOneTypeBelow B u v := by
  classical
  constructor
  · intro hEq x y hxy hyB
    have hU : (x,y) ∈ tailOneTypeCode K B u ↔
        K.edge x y u := by
      simpa only [hxy,hyB,true_and] using
        (mem_tailOneTypeCode_iff K B x y u)
    have hV : (x,y) ∈ tailOneTypeCode K B v ↔
        K.edge x y v := by
      simpa only [hxy,hyB,true_and] using
        (mem_tailOneTypeCode_iff K B x y v)
    calc
      K.edge x y u ↔ (x,y) ∈ tailOneTypeCode K B u := hU.symm
      _ ↔ (x,y) ∈ tailOneTypeCode K B v := by rw [hEq]
      _ ↔ K.edge x y v := hV
  · intro hSame
    ext p
    rcases p with ⟨x,y⟩
    rw [mem_tailOneTypeCode_iff, mem_tailOneTypeCode_iff]
    constructor
    · rintro ⟨hxy,hyB,he⟩
      exact ⟨hxy,hyB,(hSame hxy hyB).mp he⟩
    · rintro ⟨hxy,hyB,he⟩
      exact ⟨hxy,hyB,(hSame hxy hyB).mpr he⟩

/-- All possible mixed singleton types over the fixed finite cut
belong to an explicit finite set of finite edge-bit codes. -/
theorem tailOneTypeCode_mem_finite_powerset
    (K : Ordered3Graph Nat) (B v : Nat) :
    tailOneTypeCode K B v ∈ (tailOneTypeTests B).powerset := by
  classical
  exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)

end DiaryLeafPriority
end ThreeUniformDiaries
