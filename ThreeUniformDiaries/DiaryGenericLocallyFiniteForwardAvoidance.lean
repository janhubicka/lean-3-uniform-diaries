import ThreeUniformDiaries.CountableGenericEmbedding
import ThreeUniformDiaries.DiarySingletonColourCofinalCone

/-!
# Track D: avoid any locally finite forward relation inside a generic copy

Let G be an actual enumerated generic 3-uniform hypergraph, let
F : Nat -> Nat be an injective, NOT necessarily increasing map, and
let R(x,y) be an auxiliary directed relation on source vertex indices.

Suppose for every x there is a numerical target bound B_x beyond
which R(x,y) is FALSE for all y whose F(y) >= B_x.
Then we construct a single induced generic source self-embedding u
such that F ∘ u is strictly increasing and no selected forward pair
u(i),u(j), i<j, satisfies R.

At each finite stage the selected source vertices and their F-values
are both increasing. The genuine generic hypergraph extension axiom
realizes the entire required triple pattern at a source index beyond:
the old source indices, an eventual F-value order bound, AND all
finite forbidden R-neighbour bounds of the chosen earlier indices.

This is a purely combinatorial diagonal avoidance theorem, not a
relative diary extension. Crucially, a locally finite forward relation
cannot meet EVERY induced generic subcopy of a prescribed leaf range.
-/

namespace ThreeUniformDiaries
namespace DiaryLeafPriority

/-- The finite generic source copy, with the ADDITIONAL requirement
that the externally specified F-images are strictly increasing and
every already selected forward pair avoids R. -/
structure FiniteGenericForwardAvoidStage
    (G : GenericEnumerated3Graph)
    (F : Nat → Nat) (R : Nat → Nat → Prop) (n : Nat) where
  base : FiniteGenericStage G G.graph n
  target_order : StrictMono (fun i : Fin n => F (base.image i).val)
  avoids : ∀ i j : Fin n, i < j →
    ¬ R (base.image i).val (base.image j).val

namespace FiniteGenericForwardAvoidStage

/-- The empty stage vacuously avoids any forward relation. -/
def empty (G : GenericEnumerated3Graph)
    (F : Nat → Nat) (R : Nat → Nat → Prop) :
    FiniteGenericForwardAvoidStage G F R 0 where
  base := FiniteGenericStage.empty G G.graph
  target_order := by
    intro i j _
    exact Fin.elim0 i
  avoids := by
    intro i j _
    exact Fin.elim0 i

/-- The next generic source vertex can be chosen beyond all finitely
many target-value avoidance bounds, while retaining the COMPLETE
previous induced edge/nonedge table and strict F-target order. -/
theorem exists_extend
    {G : GenericEnumerated3Graph}
    {F : Nat → Nat} {R : Nat → Nat → Prop}
    {n : Nat}
    (S : FiniteGenericForwardAvoidStage G F R n)
    (hInj : Function.Injective F)
    (hFinite : ∀ x : Nat, ∃ B : Nat, ∀ y : Nat,
      B ≤ F y → ¬ R x y) :
    ∃ T : FiniteGenericForwardAvoidStage G F R (n + 1),
      ∀ i : Fin n,
        (T.base.image (Fin.castSucc i)).val =
          (S.base.image i).val := by
  classical
  let cut : Nat → Nat := fun x => Classical.choose (hFinite x)
  have hCut (x y : Nat) (hy : cut x ≤ F y) : ¬ R x y :=
    Classical.choose_spec (hFinite x) y hy
  let Q : Finset (Fin n) := Finset.univ
  let M : Nat :=
    max (Q.sup (fun i : Fin n => F (S.base.image i).val))
      (Q.sup (fun i : Fin n => cut (S.base.image i).val))
  obtain ⟨N,hLarge⟩ :=
    injective_nat_eventually_above_bound F hInj M
  let B : Nat := max S.base.bound N
  let old : Fin n → Fin B := fun i =>
    ⟨(S.base.image i).val,
      lt_of_lt_of_le (S.base.image i).isLt
        (le_max_left S.base.bound N)⟩
  have hOldMono : StrictMono old := by
    intro i j hij
    change (S.base.image i).val < (S.base.image j).val
    exact S.base.mono hij
  obtain ⟨v,hBv,hEdge,_hOutside⟩ :=
    G.exists_extension_for_source G.graph n B old hOldMono
  have hvBound : S.base.bound ≤ v :=
    (le_max_left S.base.bound N).trans hBv
  have hvN : N ≤ v := (le_max_right S.base.bound N).trans hBv
  have hFM : M < F v := hLarge v hvN
  have hTargetNew (i : Fin n) :
      F (S.base.image i).val < F v := by
    have hSup : F (S.base.image i).val ≤
        Q.sup (fun j : Fin n => F (S.base.image j).val) :=
      Finset.le_sup (f := fun j : Fin n => F (S.base.image j).val)
        (Finset.mem_univ i)
    have hM : F (S.base.image i).val ≤ M :=
      hSup.trans (le_max_left _ _)
    exact lt_of_le_of_lt hM hFM
  have hAvoidNew (i : Fin n) :
      ¬ R (S.base.image i).val v := by
    have hSup : cut (S.base.image i).val ≤
        Q.sup (fun j : Fin n => cut (S.base.image j).val) :=
      Finset.le_sup
        (f := fun j : Fin n => cut (S.base.image j).val)
        (Finset.mem_univ i)
    have hM : cut (S.base.image i).val ≤ M :=
      hSup.trans (le_max_right _ _)
    exact hCut _ v (hM.trans hFM.le)
  let image' := appendImage S.base.image hvBound
  let newBase : FiniteGenericStage G G.graph (n + 1) := {
    bound := v + 1
    image := image'
    mono := appendImage_strictMono S.base.image hvBound S.base.mono
    edge_iff := by
      intro i j k hij hjk
      have hi : i.val < n := by omega
      have hj : j.val < n := by omega
      by_cases hk : k.val < n
      · have hOld :=
          S.base.edge_iff ⟨i.val,hi⟩ ⟨j.val,hj⟩ ⟨k.val,hk⟩ hij hjk
        simpa [image', appendImage,hi,hj,hk] using hOld
      · have hkval : k.val = n := by omega
        have hNew :
            G.graph.edge i.val j.val n ↔
              G.graph.edge
                (S.base.image ⟨i.val,hi⟩).val
                (S.base.image ⟨j.val,hj⟩).val v := by
          simpa [old] using
            (hEdge ⟨i.val,hi⟩ ⟨j.val,hj⟩ hij)
        simpa [image',appendImage,hi,hj,hk,hkval] using hNew
  }
  let next : FiniteGenericForwardAvoidStage G F R (n + 1) := {
    base := newBase
    target_order := by
      intro i j hij
      have hi : i.val < n := by omega
      by_cases hj : j.val < n
      · have h : F (S.base.image ⟨i.val,hi⟩).val <
            F (S.base.image ⟨j.val,hj⟩).val :=
          S.target_order hij
        simpa [newBase,image',appendImage,hi,hj] using h
      · have h := hTargetNew ⟨i.val,hi⟩
        simpa [newBase,image',appendImage,hi,hj] using h
    avoids := by
      intro i j hij
      have hi : i.val < n := by omega
      by_cases hj : j.val < n
      · have h : ¬ R
            (S.base.image ⟨i.val,hi⟩).val
            (S.base.image ⟨j.val,hj⟩).val :=
          S.avoids ⟨i.val,hi⟩ ⟨j.val,hj⟩ hij
        simpa [newBase,image',appendImage,hi,hj] using h
      · have h := hAvoidNew ⟨i.val,hi⟩
        simpa [newBase,image',appendImage,hi,hj] using h
  }
  refine ⟨next,?_⟩
  intro i
  change (image' (Fin.castSucc i)).val = (S.base.image i).val
  exact appendImage_old S.base.image hvBound i

end FiniteGenericForwardAvoidStage

namespace GenericEnumerated3Graph

/-- A coherent sequence of genuine finite induced generic copies
whose F-images are ordered and which avoid all selected R-pairs. -/
noncomputable def forwardAvoidStages
    (G : GenericEnumerated3Graph)
    (F : Nat → Nat) (R : Nat → Nat → Prop)
    (hInj : Function.Injective F)
    (hFinite : ∀ x : Nat, ∃ B : Nat, ∀ y : Nat,
      B ≤ F y → ¬ R x y) :
    (n : Nat) → FiniteGenericForwardAvoidStage G F R n
  | 0 => FiniteGenericForwardAvoidStage.empty G F R
  | n + 1 => Classical.choose
      ((G.forwardAvoidStages F R hInj hFinite n).exists_extend
        hInj hFinite)

/-- Literal agreement of successive selected source indices. -/
theorem forwardAvoidStages_succ_old
    (G : GenericEnumerated3Graph)
    (F : Nat → Nat) (R : Nat → Nat → Prop)
    (hInj : Function.Injective F)
    (hFinite : ∀ x : Nat, ∃ B : Nat, ∀ y : Nat,
      B ≤ F y → ¬ R x y)
    (n : Nat) (i : Fin n) :
    ((G.forwardAvoidStages F R hInj hFinite (n + 1)).base.image
      (Fin.castSucc i)).val =
    ((G.forwardAvoidStages F R hInj hFinite n).base.image i).val := by
  exact (Classical.choose_spec
    ((G.forwardAvoidStages F R hInj hFinite n).exists_extend
      hInj hFinite)) i

/-- Stable finite stage images across all later stages. -/
theorem forwardAvoidStages_stable
    (G : GenericEnumerated3Graph)
    (F : Nat → Nat) (R : Nat → Nat → Prop)
    (hInj : Function.Injective F)
    (hFinite : ∀ x : Nat, ∃ B : Nat, ∀ y : Nat,
      B ≤ F y → ¬ R x y)
    (n m : Nat) (hnm : n ≤ m) (i : Fin n) :
    ((G.forwardAvoidStages F R hInj hFinite m).base.image
      ⟨i.val, by omega⟩).val =
    ((G.forwardAvoidStages F R hInj hFinite n).base.image i).val := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
      calc
        ((G.forwardAvoidStages F R hInj hFinite (m + 1)).base.image
          ⟨i.val, by omega⟩).val =
          ((G.forwardAvoidStages F R hInj hFinite m).base.image
            ⟨i.val, by omega⟩).val := by
            exact G.forwardAvoidStages_succ_old F R hInj hFinite
              m ⟨i.val, by omega⟩
        _ = ((G.forwardAvoidStages F R hInj hFinite n).base.image i).val :=
          ih

/-- The pointwise limit of the coherently chosen finite stages. -/
noncomputable def forwardAvoidEmbedding
    (G : GenericEnumerated3Graph)
    (F : Nat → Nat) (R : Nat → Nat → Prop)
    (hInj : Function.Injective F)
    (hFinite : ∀ x : Nat, ∃ B : Nat, ∀ y : Nat,
      B ≤ F y → ¬ R x y)
    (i : Nat) : Nat :=
  ((G.forwardAvoidStages F R hInj hFinite (i + 1)).base.image
    (Fin.last i)).val

theorem forwardAvoidEmbedding_at_stage
    (G : GenericEnumerated3Graph)
    (F : Nat → Nat) (R : Nat → Nat → Prop)
    (hInj : Function.Injective F)
    (hFinite : ∀ x : Nat, ∃ B : Nat, ∀ y : Nat,
      B ≤ F y → ¬ R x y)
    {i n : Nat} (hin : i < n) :
    ((G.forwardAvoidStages F R hInj hFinite n).base.image
      ⟨i,hin⟩).val =
    G.forwardAvoidEmbedding F R hInj hFinite i := by
  have hi := G.forwardAvoidStages_stable F R hInj hFinite
    (i + 1) n (by omega) (Fin.last i)
  simpa [forwardAvoidEmbedding] using hi

/-- The limit is an induced source self-embedding; its external
F-values ALSO increase strictly, and all selected forward
pairs avoid R. The F-map itself need NOT be increasing. -/
theorem exists_generic_selfembedding_avoiding_finite_forward
    (G : GenericEnumerated3Graph)
    (F : Nat → Nat) (hInj : Function.Injective F)
    (R : Nat → Nat → Prop)
    (hFinite : ∀ x : Nat, ∃ B : Nat, ∀ y : Nat,
      B ≤ F y → ¬ R x y) :
    ∃ u : Ordered3Graph.Embedding G.graph G.graph,
      StrictMono (fun t : Nat => F (u t)) ∧
      ∀ i j : Nat, i < j → ¬ R (u i) (u j) := by
  let f := G.forwardAvoidEmbedding F R hInj hFinite
  have hf : StrictMono f := by
    intro a b hab
    let S := G.forwardAvoidStages F R hInj hFinite (b + 1)
    have h := S.base.mono
      (show (⟨a, by omega⟩ : Fin (b + 1)) < Fin.last b from hab)
    change (S.base.image ⟨a, by omega⟩).val <
      (S.base.image (Fin.last b)).val at h
    simpa [f,forwardAvoidEmbedding,S,
      G.forwardAvoidEmbedding_at_stage F R hInj hFinite
        (show a < b + 1 by omega)] using h
  have hFmono : StrictMono (fun t : Nat => F (f t)) := by
    intro a b hab
    let S := G.forwardAvoidStages F R hInj hFinite (b + 1)
    have h := S.target_order
      (show (⟨a,by omega⟩ : Fin (b + 1)) < Fin.last b from hab)
    change F (S.base.image ⟨a,by omega⟩).val <
      F (S.base.image (Fin.last b)).val at h
    simpa [f,forwardAvoidEmbedding,S,
      G.forwardAvoidEmbedding_at_stage F R hInj hFinite
        (show a < b + 1 by omega)] using h
  have hEdge : ∀ a b c : Nat, a < b → b < c →
      (G.graph.edge a b c ↔ G.graph.edge (f a) (f b) (f c)) := by
    intro a b c hab hbc
    let S := G.forwardAvoidStages F R hInj hFinite (c + 1)
    have h := S.base.edge_iff
      ⟨a,by omega⟩ ⟨b,by omega⟩ (Fin.last c)
      (show a < b from hab) (show b < c from hbc)
    have ha : (S.base.image ⟨a,by omega⟩).val = f a :=
      G.forwardAvoidEmbedding_at_stage F R hInj hFinite (by omega)
    have hb : (S.base.image ⟨b,by omega⟩).val = f b :=
      G.forwardAvoidEmbedding_at_stage F R hInj hFinite (by omega)
    have hc : (S.base.image (Fin.last c)).val = f c :=
      G.forwardAvoidEmbedding_at_stage F R hInj hFinite
        (Nat.lt_succ_self c)
    rw [ha,hb,hc] at h
    exact h
  let u : Ordered3Graph.Embedding G.graph G.graph := {
    toFun := f
    strictMono := hf
    edge_iff := hEdge
  }
  refine ⟨u,hFmono,?_⟩
  intro i j hij
  let S := G.forwardAvoidStages F R hInj hFinite (j + 1)
  have h := S.avoids
    (⟨i,by omega⟩ : Fin (j+1)) (Fin.last j) hij
  have hi : (S.base.image ⟨i,by omega⟩).val = f i :=
    G.forwardAvoidEmbedding_at_stage F R hInj hFinite (by omega)
  have hj : (S.base.image (Fin.last j)).val = f j :=
    G.forwardAvoidEmbedding_at_stage F R hInj hFinite
      (Nat.lt_succ_self j)
  simpa [u,hi,hj] using h

end GenericEnumerated3Graph
end DiaryLeafPriority
end ThreeUniformDiaries
