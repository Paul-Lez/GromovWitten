/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Curves.FibreDimension
import GromovWitten.AlgebraicGeometry.Stacks.OverlapSwap

/-!
# The dimension formula for flat morphisms of schemes of finite type over a field

For a flat morphism `q : W ⟶ U`, locally of finite presentation, between schemes locally of
finite type over a field `K`, with `U` pure of dimension `a` and every fibre of `q` pure of
dimension `r`, the scheme `W` is pure of dimension `a + r`
(`pureTopologicalDimension_of_flat_of_pureRelativeDimension`).  In particular the smooth
dimension formula `SmoothPureDimensionFormulaAt q` of `Stacks/OverlapSwap.lean` holds for every
smooth morphism between schemes locally of finite type over a field
(`smoothPureDimensionFormulaAt_of_locallyOfFiniteType`), and the dimension of an algebraic stack
whose atlas schemes are locally of finite type over a field is independent of the atlas
(`stackDimensionIndependent_of_atlasLocallyOfFiniteTypeOver`).

## The argument

Let `Z` be an irreducible component of `W` with generic point `η`, and let `ξ = q η`.

* `topologicalKrullDim (closure {x}) = Order.height x` for every point `x` of a scheme
  (`topologicalKrullDim_closure_singleton`): the closed irreducible subsets of `closure {x}`
  are its points, i.e. the specializations of `x`.
* The upper bound `height η ≤ a + r` is the fibre-dimension inequality
  `Curves.height_le_of_fibers` of `Curves/FibreDimension.lean`.
* For the lower bound, `q` is generalizing (flat), so `ξ` is the generic point of an irreducible
  component of `U` (`closure_singleton_map_mem_irreducibleComponents`) and has height `a`; the
  point `η` regarded in the fibre `q.fiber ξ` is the generic point of an irreducible component
  of the fibre (`closure_singleton_asFiber_mem_irreducibleComponents`) and has height `r`
  there.  A chain of length `r` in the fibre ending at `η` maps to a chain in `W` starting at a
  point `x₀` over `ξ`, and `height x₀ ≥ height ξ = a` because over a field the height of a point
  is the transcendence degree of its residue field (`height_eq_toENat_trdeg`, from
  `Curves/FibreDimension.lean` and `Algebra/FiniteTypeKrullDimension.lean`), which can only
  grow along the residue field extension `κ(ξ) ⊆ κ(x₀)` (`height_apply_le_height`).
  Concatenating a chain of length `a` below `x₀` with the chain of length `r` gives
  `height η ≥ a + r`.

No result is a field of a structure; there is no `sorry` and no new axiom.
-/

open CategoryTheory Limits Topology TopologicalSpace
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

/-! ### Generic points of irreducible components -/

section Topology

variable {X : Scheme.{u}}

/-- The closure of a point is an irreducible component exactly when the point has no proper
generization. -/
theorem closure_singleton_mem_irreducibleComponents_iff (x : X) :
    closure ({x} : Set X) ∈ irreducibleComponents X ↔ ∀ y : X, y ⤳ x → y = x := by
  constructor
  · intro h y hy
    have hsub : closure ({x} : Set X) ⊆ closure {y} := specializes_iff_closure_subset.mp hy
    have hsub' : closure ({y} : Set X) ⊆ closure {x} :=
      h.2 isIrreducible_singleton.closure hsub
    exact (inseparable_iff_closure_eq.mpr (hsub'.antisymm hsub)).eq
  · intro h
    refine ⟨isIrreducible_singleton.closure, fun S hS hsub ↦ ?_⟩
    have hg := hS.isGenericPoint_genericPoint_closure
    have hxS : x ∈ closure S := subset_closure (hsub (subset_closure (Set.mem_singleton x)))
    have hgx : hS.genericPoint = x := h _ (hg.specializes hxS)
    have hcl : closure S = closure {x} := by rw [← hg.def, hgx]
    exact subset_closure.trans hcl.le

/-- The dimension of the closure of a point is the height of the point in the specialization
order: the closed irreducible subsets of `closure {x}` are the closures of the specializations
of `x`. -/
theorem topologicalKrullDim_closure_singleton (x : X) :
    topologicalKrullDim (closure ({x} : Set X)) = ((Order.height x : ℕ∞) : WithBot ℕ∞) := by
  have hC : IsClosed (closure ({x} : Set X)) := isClosed_closure
  have : QuasiSober (closure ({x} : Set X)) := hC.isClosedEmbedding_subtypeVal.quasiSober
  let _ : PartialOrder (closure ({x} : Set X)) := specializationOrder _
  rw [Order.height_eq_krullDim_Iic]
  change Order.krullDim (IrreducibleCloseds (closure ({x} : Set X))) = _
  have h1 := @Order.krullDim_eq_of_orderIso (IrreducibleCloseds (closure ({x} : Set X)))
    (closure ({x} : Set X)) _ (specializationOrder _).toPreorder irreducibleSetEquivPoints
  rw [h1]
  have hset : closure ({x} : Set X) = Set.Iic x := by
    ext y
    change y ∈ closure ({x} : Set X) ↔ x ⤳ y
    exact specializes_iff_mem_closure.symm
  let e : @OrderIso (closure ({x} : Set X)) (Set.Iic x) (specializationOrder _).toLE _ :=
    { toEquiv := Equiv.setCongr hset
      map_rel_iff' := fun {a b} ↦ by
        change ((b : X) ⤳ (a : X)) ↔ (b ⤳ a)
        exact IsInducing.subtypeVal.specializes_iff }
  exact @Order.krullDim_eq_of_orderIso (closure ({x} : Set X)) (Set.Iic x)
    (specializationOrder _).toPreorder _ e

/-- A generalizing map sends the generic point of an irreducible component to the generic point
of an irreducible component. -/
theorem closure_singleton_map_mem_irreducibleComponents {W U : Scheme.{u}} (q : W ⟶ U)
    (hq : GeneralizingMap q) {η : W} (hη : closure ({η} : Set W) ∈ irreducibleComponents W) :
    closure ({q η} : Set U) ∈ irreducibleComponents U := by
  rw [closure_singleton_mem_irreducibleComponents_iff] at hη ⊢
  intro ξ hξ
  obtain ⟨η', hη', rfl⟩ := hq hξ
  rw [hη η' hη']

/-- The generic point of an irreducible component of `W`, regarded as a point of the fibre of
`q` through it, is the generic point of an irreducible component of that fibre. -/
theorem closure_singleton_asFiber_mem_irreducibleComponents {W U : Scheme.{u}} (q : W ⟶ U)
    {η : W} (hη : closure ({η} : Set W) ∈ irreducibleComponents W) :
    closure ({q.asFiber η} : Set (q.fiber (q η))) ∈ irreducibleComponents (q.fiber (q η)) := by
  rw [closure_singleton_mem_irreducibleComponents_iff] at hη ⊢
  intro y hy
  have h1 : q.fiberι (q η) y ⤳ q.fiberι (q η) (q.asFiber η) :=
    hy.map (q.fiberι (q η)).continuous
  rw [Scheme.Hom.fiberι_asFiber] at h1
  have h2 := hη _ h1
  exact (q.fiberι (q η)).isEmbedding.injective (h2.trans (Scheme.Hom.fiberι_asFiber q η).symm)

/-- An embedding of schemes is strictly monotone for the specialization orders. -/
theorem strictMono_of_isEmbedding {Y Z : Scheme.{u}} (j : Y ⟶ Z) (hj : IsEmbedding j) :
    StrictMono j := by
  intro a b hab
  rw [lt_iff_le_not_ge] at hab ⊢
  change (b ⤳ a) ∧ ¬ (a ⤳ b) at hab
  change (j b ⤳ j a) ∧ ¬ (j a ⤳ j b)
  rwa [hj.isInducing.specializes_iff, hj.isInducing.specializes_iff]

/-- Every point of the fibre of `q` over `ξ` maps to `ξ`. -/
theorem apply_fiberι {W U : Scheme.{u}} (q : W ⟶ U) (ξ : U) (z : q.fiber ξ) :
    q (q.fiberι ξ z) = ξ := by
  have h := (q.fiberHomeo ξ z).2
  simpa using h

end Topology

/-! ### Heights of points over a field -/

section Field

variable {K : Type u} [Field K]

/-- Over a field, the height of a point of a scheme locally of finite type (the dimension of its
closure) is the transcendence degree of its residue field. -/
theorem height_eq_toENat_trdeg {Z : Scheme.{u}} (π : Z ⟶ Spec (.of K))
    [LocallyOfFiniteType π] (z : Z) :
    letI := stalkResidueFieldAlgebra π z
    (Order.height z : ℕ∞) =
      Cardinal.toENat (Algebra.trdeg K (IsLocalRing.ResidueField (Z.presheaf.stalk z))) := by
  obtain ⟨V, hV, hz, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := z) trivial
  let _ := sectionsAlgebra π V
  let _ := stalkResidueFieldAlgebra π z
  have h1 : Algebra.FiniteType K Γ(Z, V) := sectionsAlgebra_finiteType π hV
  have e1 := GromovWitten.Algebra.PrimeSpectrum.coheight_eq_toENat_trdeg_residueField (k := K)
    (hV.primeIdealOf ⟨z, hz⟩)
  have e2 := (chartResidueFieldAlgEquiv π hV hz).trdeg_eq
  rw [height_eq_coheight_primeIdealOf π hV hz, e1, e2]

/-- The residue field map of `q` at `x` is a `K`-algebra homomorphism for the `K`-algebra
structures induced by the structure morphisms. -/
def residueFieldAlgHom {W U : Scheme.{u}} (q : W ⟶ U) (πU : U ⟶ Spec (.of K)) (x : W) :
    letI := stalkResidueFieldAlgebra πU (q x)
    letI := stalkResidueFieldAlgebra (q ≫ πU) x
    IsLocalRing.ResidueField (U.presheaf.stalk (q x)) →ₐ[K]
      IsLocalRing.ResidueField (W.presheaf.stalk x) :=
  letI := stalkResidueFieldAlgebra πU (q x)
  letI := stalkResidueFieldAlgebra (q ≫ πU) x
  { (q.residueFieldMap x).hom with
    commutes' := fun c ↦ by
      have key : (q.residueFieldMap x).hom.comp ((U.residue (q x)).hom.comp
          ((U.presheaf.germ (πU ⁻¹ᵁ ⊤) (q x) (@id (q x ∈ πU ⁻¹ᵁ ⊤) (by simp))).hom.comp
            ((πU.app ⊤).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom))) =
          (W.residue x).hom.comp ((W.presheaf.germ ((q ≫ πU) ⁻¹ᵁ ⊤) x
            (@id (x ∈ (q ≫ πU) ⁻¹ᵁ ⊤) (by simp))).hom.comp
            (((q ≫ πU).app ⊤).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom)) := by
        rw [← RingHom.comp_assoc, ← CommRingCat.hom_comp, Scheme.residue_residueFieldMap,
          CommRingCat.hom_comp, RingHom.comp_assoc, ← RingHom.comp_assoc (h := (q.stalkMap x).hom),
          ← CommRingCat.hom_comp, Scheme.Hom.germ_stalkMap, CommRingCat.hom_comp,
          RingHom.comp_assoc]
        rfl
      exact congrArg (fun φ ↦ φ c) key }

/-- Along a morphism of schemes locally of finite type over a field, the height of a point is
at least the height of its image: the residue field of the image embeds into the residue field
of the point, and transcendence degree is monotone. -/
theorem height_apply_le_height {W U : Scheme.{u}} (q : W ⟶ U) (πU : U ⟶ Spec (.of K))
    [LocallyOfFiniteType πU] [LocallyOfFiniteType (q ≫ πU)] (x : W) :
    Order.height (q x) ≤ Order.height x := by
  let _ := stalkResidueFieldAlgebra πU (q x)
  let _ := stalkResidueFieldAlgebra (q ≫ πU) x
  have h1 := height_eq_toENat_trdeg πU (q x)
  have h2 := height_eq_toENat_trdeg (q ≫ πU) x
  rw [h1, h2]
  exact OrderHomClass.monotone Cardinal.toENat
    (trdeg_le_of_injective (residueFieldAlgHom q πU x) (RingHom.injective _))

end Field

/-! ### The dimension formula -/

section Formula

variable {K : Type u} [Field K]

/-- **The dimension formula.**  Let `q : W ⟶ U` be flat and locally of finite presentation
between schemes locally of finite type over a field `K`.  If `U` is pure of dimension `a` and
every fibre of `q` is pure of dimension `r`, then `W` is pure of dimension `a + r`. -/
theorem pureTopologicalDimension_of_flat_of_pureRelativeDimension {W U : Scheme.{u}}
    (q : W ⟶ U) (πU : U ⟶ Spec (.of K)) [LocallyOfFiniteType πU] [Flat q]
    [LocallyOfFinitePresentation q] {a r : ℕ} (hq : PureRelativeDimension r q)
    (hU : PureTopologicalDimension a U) : PureTopologicalDimension (a + r) W := by
  have : LocallyOfFiniteType (q ≫ πU) := inferInstance
  intro Z hZ
  have hZirr : IsIrreducible Z := hZ.1
  have hZcl : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  have hgen : IsGenericPoint hZirr.genericPoint Z := hZirr.isGenericPoint_genericPoint hZcl
  set η := hZirr.genericPoint with hηdef
  have hZeq : Z = closure {η} := hgen.def.symm
  rw [hZeq] at hZ ⊢
  rw [topologicalKrullDim_closure_singleton]
  -- the upper bound
  have hup : Order.height η ≤ (r + a : ℕ) :=
    height_le_of_fibers q πU (topologicalKrullDim_le_of_pure hU)
      (fun ξ ↦ topologicalKrullDim_le_of_pure (hq.2 ξ)) η
  -- the image of `η` is the generic point of a component of `U`
  have hξc : closure ({q η} : Set U) ∈ irreducibleComponents U :=
    closure_singleton_map_mem_irreducibleComponents q (Flat.generalizingMap q) hZ
  have hξh : Order.height (q η) = a := by
    have h := hU _ hξc
    rw [topologicalKrullDim_closure_singleton] at h
    exact_mod_cast h
  -- `η` is the generic point of a component of its fibre
  have hyc := closure_singleton_asFiber_mem_irreducibleComponents q hZ
  have hyh : Order.height (q.asFiber η) = r := by
    have h := hq.2 (q η) _ hyc
    rw [topologicalKrullDim_closure_singleton] at h
    exact_mod_cast h
  obtain ⟨p, hpl, hpn⟩ := Order.exists_series_of_le_height (q.asFiber η) (n := r) hyh.ge
  let p' : LTSeries W := p.map (q.fiberι (q η))
    (strictMono_of_isEmbedding _ (q.fiberι (q η)).isEmbedding)
  have hp'l : p'.last = η := by
    rw [LTSeries.last_map, hpl, Scheme.Hom.fiberι_asFiber]
  have hx₀ : q p'.head = q η := by
    rw [LTSeries.head_map]
    exact apply_fiberι q (q η) p.head
  have hx₀h : (a : ℕ∞) ≤ Order.height p'.head := by
    have h := height_apply_le_height q πU p'.head
    rw [hx₀, hξh] at h
    exact h
  obtain ⟨s, hsl, hsn⟩ := Order.exists_series_of_le_height p'.head hx₀h
  have hlow : ((a + r : ℕ) : ℕ∞) ≤ Order.height η := by
    have h := Order.length_le_height_last (p := s.smash p' hsl)
    rw [RelSeries.last_smash, hp'l] at h
    have hlen : (s.smash p' hsl).length = a + r := by
      change s.length + p'.length = a + r
      rw [hsn]
      change a + p.length = a + r
      rw [hpn]
    rw [hlen] at h
    exact_mod_cast h
  have hη : Order.height η = ((a + r : ℕ) : ℕ∞) := by
    refine le_antisymm ?_ hlow
    rw [add_comm a r]
    exact hup
  rw [hη]
  rfl

/-- The smooth dimension formula of `Stacks/OverlapSwap.lean` holds for every smooth morphism
between schemes locally of finite type over a field. -/
theorem smoothPureDimensionFormulaAt_of_locallyOfFiniteType {W U : Scheme.{u}} (q : W ⟶ U)
    (πU : U ⟶ Spec (.of K)) [LocallyOfFiniteType πU] :
    SmoothPureDimensionFormulaAt q := by
  intro r a hsmooth _ hrel hU
  have : _root_.AlgebraicGeometry.Smooth q := hsmooth
  exact pureTopologicalDimension_of_flat_of_pureRelativeDimension q πU hrel hU

end Formula

/-! ### Atlas independence of the dimension of a stack of finite type over a field -/

section Stack

variable {K : Type u} [Field K]

/-- An algebraic stack is locally of finite type over the field `K` in the sense used here when
the scheme of every atlas dimension presentation carries a structure morphism to `Spec K`
which is locally of finite type. -/
def AtlasLocallyOfFiniteTypeOver (K : Type u) [Field K] (X : AlgebraicStack.{u}) : Prop :=
  ∀ A : StackDimensionPresentation X,
    ∃ π : A.atlas.scheme ⟶ Spec (.of K), LocallyOfFiniteType π

/-- For a stack whose atlas schemes are locally of finite type over a field, the dimension
formula holds for both projections of every overlap of two atlases. -/
theorem overlapDimensionFormula_of_atlasLocallyOfFiniteTypeOver {X : AlgebraicStack.{u}}
    (hX : AtlasLocallyOfFiniteTypeOver K X) : OverlapDimensionFormula X := by
  intro A B
  obtain ⟨πA, hπA⟩ := hX A
  obtain ⟨πB, hπB⟩ := hX B
  exact ⟨smoothPureDimensionFormulaAt_of_locallyOfFiniteType _ πB,
    smoothPureDimensionFormulaAt_of_locallyOfFiniteType _ πA⟩

/-- **Atlas independence of the dimension** for stacks whose atlas schemes are locally of finite
type over a field with non-empty atlases. -/
theorem stackDimensionIndependent_of_atlasLocallyOfFiniteTypeOver {X : AlgebraicStack.{u}}
    (hX : AtlasLocallyOfFiniteTypeOver K X)
    (hne : ∀ A : StackDimensionPresentation X, Nonempty A.atlas.scheme) :
    StackDimensionIndependent X :=
  stackDimensionIndependent_of_overlapDimensionFormula
    (overlapDimensionFormula_of_atlasLocallyOfFiniteTypeOver hX) hne

/-- The dimension of a stack of finite type over a field is computed by any atlas. -/
theorem AlgebraicStack.dim_eq_of_atlasLocallyOfFiniteTypeOver {X : AlgebraicStack.{u}}
    (hX : AtlasLocallyOfFiniteTypeOver K X)
    (hne : ∀ A : StackDimensionPresentation X, Nonempty A.atlas.scheme)
    (A : StackDimensionPresentation X) :
    X.dim = StackDim.ofInt A.correctedDimension :=
  AlgebraicStack.dim_eq_of_overlapDimensionFormula
    (overlapDimensionFormula_of_atlasLocallyOfFiniteTypeOver hX) hne A

end Stack

end

end GromovWitten.AlgebraicGeometry.Curves
