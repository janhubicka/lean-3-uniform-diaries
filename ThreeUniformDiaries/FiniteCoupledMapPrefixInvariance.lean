import ThreeUniformDiaries.FiniteAuxMapPrefixInvariance
import ThreeUniformDiaries.FiniteCoupledCanonicalMaps

/-!
# Finite E1/E0 canonical maps ignore all unselected future heights

A finite synchronized three-coordinate strong picture only uses its
selected levels through k. We extend the concrete E2 tail-independence
lemma to the E1 recursion (using E2 boundary parameters), then to E0
(using E1 boundary parameters).

The proof is on actual ambient type nodes, avoiding casts between
different dependently indexed OneNode/EnumNode types. Both recursions
select their next image by uniqueness in the same immediate successor
cone of the same finite strong carrier.

No arbitrary continuation of finite heights can change the value of
the manuscript's finite F_I map on any branch of index at most k.
-/

namespace ThreeUniformDiaries
namespace CoordNode

private def oneAppendAux : CoordNode → CoordNode → CoordNode
  | .one n a, .aux m c =>
      if h : n = m then .one (n + 1) (a.succ (h.symm ▸ c))
      else zeroChild (.one n a)
  | x, _ => zeroChild x

private def enumAppendOne : CoordNode → CoordNode → CoordNode
  | .enum n a, .one m c =>
      if h : n = m then .enum (n + 1) (a.succ (h.symm ▸ c))
      else zeroChild (.enum n a)
  | x, _ => zeroChild x

private theorem one_node_cast {n m : Nat} (h : n = m) (a : OneNode n) :
    CoordNode.one n a =
      CoordNode.one m (Eq.mp (congrArg OneNode h) a) := by
  cases h
  rfl

private theorem enum_node_cast {n m : Nat} (h : n = m) (a : EnumNode n) :
    CoordNode.enum n a =
      CoordNode.enum m (Eq.mp (congrArg EnumNode h) a) := by
  cases h
  rfl

/-- Literal ambient singleton canonical images are the same whenever
their finite strong carriers and first k+1 source heights agree. -/
theorem finiteOneCanonicalMap_eq_of_prefix_heights
    {S₁ S₂ : Set CoordNode} {f g : Nat → Nat} {k : Nat}
    {rf₁ : OneNode (f 0)} {rf₂ : AuxNode (f 0)}
    {rg₁ : OneNode (g 0)} {rg₂ : AuxNode (g 0)}
    (hF₁ : FiniteStrongPicture S₁ f k (.one (f 0) rf₁))
    (hF₂ : FiniteStrongPicture S₂ f k (.aux (f 0) rf₂))
    (hG₁ : FiniteStrongPicture S₁ g k (.one (g 0) rg₁))
    (hG₂ : FiniteStrongPicture S₂ g k (.aux (g 0) rg₂))
    (heights : ∀ i : Nat, i ≤ k → f i = g i) :
    ∀ (i : Nat) (hi : i ≤ k) (a : OneNode i),
      CoordNode.one (f i)
        (finiteStrongPicture_oneCanonicalMap hF₁ hF₂ i hi a).val =
      CoordNode.one (g i)
        (finiteStrongPicture_oneCanonicalMap hG₁ hG₂ i hi a).val := by
  intro i
  induction i with
  | zero =>
      intro hi a
      change CoordNode.one (f 0) rf₁ =
        CoordNode.one (g 0) rg₁
      exact finiteStrongPicture_root_unique_of_carrier hF₁ hG₁
  | succ i ih =>
      intro hi a
      have hik : i < k := by omega
      have hi0 : i ≤ k := by omega
      let prevF := finiteStrongPicture_oneCanonicalMap
        hF₁ hF₂ i hi0 (a.truncate i)
      let prevG := finiteStrongPicture_oneCanonicalMap
        hG₁ hG₂ i hi0 (a.truncate i)
      let paramF := finiteStrongPicture_auxCanonicalMap
        hF₂ i hi0 (a.boundaryAux i)
      let paramG := finiteStrongPicture_auxCanonicalMap
        hG₂ i hi0 (a.boundaryAux i)
      let curF := finiteStrongPicture_oneCanonicalMap
        hF₁ hF₂ (i + 1) hi a
      let curG := finiteStrongPicture_oneCanonicalMap
        hG₁ hG₂ (i + 1) hi a
      have hprev :
          CoordNode.one (f i) prevF.val =
            CoordNode.one (g i) prevG.val := ih hi0 (a.truncate i)
      have hparam :
          CoordNode.aux (f i) paramF.val =
            CoordNode.aux (g i) paramG.val :=
        finiteAuxCanonicalMap_eq_of_prefix_heights
          hF₂ hG₂ heights i hi0 (a.boundaryAux i)
      have hchild :
          CoordNode.one (f i + 1) (prevF.val.succ paramF.val) =
          CoordNode.one (g i + 1) (prevG.val.succ paramG.val) := by
        simpa [oneAppendAux] using
          congrArg₂ oneAppendAux hprev hparam
      have hspecF :
          CoordNode.one (f (i + 1)) curF.val ∈ S₁ ∧
          CoordNode.one (f i + 1) (prevF.val.succ paramF.val) ≤
            CoordNode.one (f (i + 1)) curF.val :=
        finiteStrongPicture_oneStep_spec hF₁
          i hik prevF.val prevF.property paramF.val
      have hspecG :
          CoordNode.one (g (i + 1)) curG.val ∈ S₁ ∧
          CoordNode.one (g i + 1) (prevG.val.succ paramG.val) ≤
            CoordNode.one (g (i + 1)) curG.val :=
        finiteStrongPicture_oneStep_spec hG₁
          i hik prevG.val prevG.property paramG.val
      have hheight : g (i + 1) = f (i + 1) :=
        (heights (i + 1) hi).symm
      let q : OneNode (f (i + 1)) :=
        Eq.mp (congrArg OneNode hheight) curG.val
      have hqNode :
          CoordNode.one (g (i + 1)) curG.val =
            CoordNode.one (f (i + 1)) q :=
        one_node_cast hheight curG.val
      have hqMem : CoordNode.one (f (i + 1)) q ∈ S₁ := by
        rw [← hqNode]
        exact hspecG.1
      have hqCone :
          CoordNode.one (f i + 1) (prevF.val.succ paramF.val) ≤
            CoordNode.one (f (i + 1)) q := by
        rw [← hqNode, hchild]
        exact hspecG.2
      obtain ⟨w, _, hunique⟩ :=
        finiteStrongPicture_one_lift hF₁ i hik
          prevF.val prevF.property paramF.val
      have hFVal : curF.val = w :=
        hunique curF.val hspecF
      have hGVal : q = w :=
        hunique q ⟨hqMem, hqCone⟩
      calc
        CoordNode.one (f (i + 1)) curF.val =
            CoordNode.one (f (i + 1)) q := by
          rw [hFVal, hGVal]
        _ = CoordNode.one (g (i + 1)) curG.val := hqNode.symm

/-- Literal ambient enumeration canonical images are the same
for all choices of selected future levels beyond the finite cut. -/
theorem finiteEnumCanonicalMap_eq_of_prefix_heights
    {S₀ S₁ S₂ : Set CoordNode} {f g : Nat → Nat} {k : Nat}
    {rf₀ : EnumNode (f 0)} {rf₁ : OneNode (f 0)} {rf₂ : AuxNode (f 0)}
    {rg₀ : EnumNode (g 0)} {rg₁ : OneNode (g 0)} {rg₂ : AuxNode (g 0)}
    (hF₀ : FiniteStrongPicture S₀ f k (.enum (f 0) rf₀))
    (hF₁ : FiniteStrongPicture S₁ f k (.one (f 0) rf₁))
    (hF₂ : FiniteStrongPicture S₂ f k (.aux (f 0) rf₂))
    (hG₀ : FiniteStrongPicture S₀ g k (.enum (g 0) rg₀))
    (hG₁ : FiniteStrongPicture S₁ g k (.one (g 0) rg₁))
    (hG₂ : FiniteStrongPicture S₂ g k (.aux (g 0) rg₂))
    (heights : ∀ i : Nat, i ≤ k → f i = g i) :
    ∀ (i : Nat) (hi : i ≤ k) (a : EnumNode i),
      CoordNode.enum (f i)
        (finiteStrongPicture_enumCanonicalMap hF₀ hF₁ hF₂ i hi a).val =
      CoordNode.enum (g i)
        (finiteStrongPicture_enumCanonicalMap hG₀ hG₁ hG₂ i hi a).val := by
  intro i
  induction i with
  | zero =>
      intro hi a
      change CoordNode.enum (f 0) rf₀ =
        CoordNode.enum (g 0) rg₀
      exact finiteStrongPicture_root_unique_of_carrier hF₀ hG₀
  | succ i ih =>
      intro hi a
      have hik : i < k := by omega
      have hi0 : i ≤ k := by omega
      let prevF := finiteStrongPicture_enumCanonicalMap
        hF₀ hF₁ hF₂ i hi0 (a.truncate i)
      let prevG := finiteStrongPicture_enumCanonicalMap
        hG₀ hG₁ hG₂ i hi0 (a.truncate i)
      let paramF := finiteStrongPicture_oneCanonicalMap
        hF₁ hF₂ i hi0 (a.boundaryOne i)
      let paramG := finiteStrongPicture_oneCanonicalMap
        hG₁ hG₂ i hi0 (a.boundaryOne i)
      let curF := finiteStrongPicture_enumCanonicalMap
        hF₀ hF₁ hF₂ (i + 1) hi a
      let curG := finiteStrongPicture_enumCanonicalMap
        hG₀ hG₁ hG₂ (i + 1) hi a
      have hprev :
          CoordNode.enum (f i) prevF.val =
            CoordNode.enum (g i) prevG.val := ih hi0 (a.truncate i)
      have hparam :
          CoordNode.one (f i) paramF.val =
            CoordNode.one (g i) paramG.val :=
        finiteOneCanonicalMap_eq_of_prefix_heights
          hF₁ hF₂ hG₁ hG₂ heights i hi0 (a.boundaryOne i)
      have hchild :
          CoordNode.enum (f i + 1) (prevF.val.succ paramF.val) =
          CoordNode.enum (g i + 1) (prevG.val.succ paramG.val) := by
        simpa [enumAppendOne] using
          congrArg₂ enumAppendOne hprev hparam
      have hspecF :
          CoordNode.enum (f (i + 1)) curF.val ∈ S₀ ∧
          CoordNode.enum (f i + 1) (prevF.val.succ paramF.val) ≤
            CoordNode.enum (f (i + 1)) curF.val :=
        finiteStrongPicture_enumStep_spec hF₀
          i hik prevF.val prevF.property paramF.val
      have hspecG :
          CoordNode.enum (g (i + 1)) curG.val ∈ S₀ ∧
          CoordNode.enum (g i + 1) (prevG.val.succ paramG.val) ≤
            CoordNode.enum (g (i + 1)) curG.val :=
        finiteStrongPicture_enumStep_spec hG₀
          i hik prevG.val prevG.property paramG.val
      have hheight : g (i + 1) = f (i + 1) :=
        (heights (i + 1) hi).symm
      let q : EnumNode (f (i + 1)) :=
        Eq.mp (congrArg EnumNode hheight) curG.val
      have hqNode :
          CoordNode.enum (g (i + 1)) curG.val =
            CoordNode.enum (f (i + 1)) q :=
        enum_node_cast hheight curG.val
      have hqMem : CoordNode.enum (f (i + 1)) q ∈ S₀ := by
        rw [← hqNode]
        exact hspecG.1
      have hqCone :
          CoordNode.enum (f i + 1) (prevF.val.succ paramF.val) ≤
            CoordNode.enum (f (i + 1)) q := by
        rw [← hqNode, hchild]
        exact hspecG.2
      obtain ⟨w, _, hunique⟩ :=
        finiteStrongPicture_enum_lift hF₀ i hik
          prevF.val prevF.property paramF.val
      have hFVal : curF.val = w :=
        hunique curF.val hspecF
      have hGVal : q = w :=
        hunique q ⟨hqMem, hqCone⟩
      calc
        CoordNode.enum (f (i + 1)) curF.val =
            CoordNode.enum (f (i + 1)) q := by
          rw [hFVal, hGVal]
        _ = CoordNode.enum (g (i + 1)) curG.val := hqNode.symm

end CoordNode
end ThreeUniformDiaries
