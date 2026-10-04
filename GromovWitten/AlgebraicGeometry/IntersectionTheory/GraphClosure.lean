/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.ProperPushforwardChow
import GromovWitten.AlgebraicGeometry.ProjectiveLineProj

/-!
# The graph closure of a rational function

Let `V` be an integral, locally Noetherian scheme and `φ` a rational function on `V`, regular on
a nonempty quasi-compact open `U ⊆ V` (`φ = germ φ₀`, `φ₀ ∈ Γ(V, U)`; such `U` exists by
`exists_affineOpen_germ_eq`).  The *graph* of `φ₀` is the morphism `U ⟶ ℙ¹_V`,
`u ↦ (u, φ₀(u))`, landing in the first affine chart `𝔸¹_V ⊆ ℙ¹_V`; the *graph closure*
`Ṽ ⊆ ℙ¹_V` is its scheme-theoretic image, an integral closed subscheme.  This file develops the
geometry of `Ṽ` needed for the proper pushforward of principal divisors in the case where the
dimension drops by one (Fulton, *Intersection Theory*, Prop. 1.4; blueprint C.3.2):

* the projection `q : Ṽ ⟶ V` is proper and birational, so `q_* div(φ̃) = div(φ)` for the
  pullback `φ̃` of `φ` (G.3, G.4);
* for a proper dominant `h : V ⟶ V'` with `φ` transcendental over `K(V')`, the map
  `g : Ṽ ⟶ ℙ¹_{V'}` induced by `h` is proper and dominant, pulls the coordinate `t` of `ℙ¹_{V'}`
  back to `φ̃`, and, when `dim V' = dim V - 1`, satisfies `g_* div(φ̃) = d • div(t)` with
  `d = [K(Ṽ) : K(ℙ¹_{V'})]` (G.5, G.6).

The projective line `ℙ¹_S = P1.P1S S`, its projection `P1.pr S`, its affine charts and its
coordinate function come from `GromovWitten.AlgebraicGeometry.ProjectiveLineProj`.  Dimension
functions are arbitrary certified `DimensionFunction`s; the schemes are assumed locally of finite
type over a field `k` through explicit structure morphisms where dimensions are compared.

## Main results

* `GraphClosure.coheight_eq_one_iff_dim_eq_genericPoint_sub_one`,
  `GraphClosure.coheight_eq_one_of_coheight_apply_eq_one`,
  `GraphClosure.dim_eq_iff_coheight_apply_eq_one` (Lemma Dim-1): codimension-one bookkeeping
  along a proper dominant morphism of integral schemes, locally of finite type over a field, whose
  generic points have the same dimension.
* `GraphClosure.exists_affineOpen_germ_eq` (G.1): a rational function is regular on some nonempty
  affine open.
* `GraphClosure.graphMap`, `GraphClosure.graphClosure`, `GraphClosure.toGraphClosure`,
  `GraphClosure.genericPointImage_graphClosure` (G.2): the graph and its closure.
* `GraphClosure.q`, `GraphClosure.dominantFunctionFieldMap_q_bijective`,
  `GraphClosure.finrank_functionField_q`, `GraphClosure.norm_algebraMap_q` (G.3).
* `GraphClosure.dim_genericPoint_graphClosure`, `GraphClosure.map_q_principalCycle` (G.4, G.4.1).
* `GraphClosure.g`, `GraphClosure.g_pr`, `GraphClosure.g_genericPoint`,
  `GraphClosure.isDominant_g`, `GraphClosure.dim_genericPoint_eq_g` (G.5).
* `GraphClosure.dominantFunctionFieldMap_g_coordFn`, `GraphClosure.algebraMap_coordFn_eq`,
  `GraphClosure.norm_phi_tilde`, `GraphClosure.map_g_principalCycle` (G.6, G.6.1).
* `GraphClosure.map_principalCycle_of_dim_genericPoint_eq`: round 23's
  `map_principalCycle_eq_principalCycle_norm` for a proper dominant morphism out of an integral
  closed subscheme whose generic point keeps its dimension (over a field).
* Auxiliary: `GraphClosure.resTrdeg_add_one_le_of_transcendental` (a transcendental element of
  `κ(x)` over `κ(p x)` raises the residue transcendence degree),
  `GraphClosure.transcendental_residue_genericPoint`,
  `GraphClosure.dominantFunctionFieldMap_germToFunctionField`.
-/

-- Concrete `Spec R` / section-ring / residue-field carriers only unify with the generic scheme
-- instances at default transparency; this option is what Mathlib's own affine-scheme API uses.
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace Order

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory

namespace GraphClosure

/-! ## Lemma Dim-1: codimension one along an equidimensional proper dominant morphism -/

section DimOne

variable {k : Type u} [Field k] {A B : Scheme.{u}} [IsIntegral A] [IsIntegral B]

/-- On an integral scheme locally of finite type over a field, a point has coheight one exactly
when its dimension is one less than that of the generic point. -/
theorem coheight_eq_one_iff_dim_eq_genericPoint_sub_one
    (sA : A ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sA] (dA : DimensionFunction A)
    (x : A) : coheight x = 1 ↔ dA x = dA (genericPoint A) - 1 := by
  rw [HomogeneityLocal.coheight_eq_one_iff_covBy (HomogeneityLocal.isTop_genericPoint A)]
  constructor
  · intro hc
    have := covByDimension_of_locallyOfFiniteType sA dA _ _ hc
    omega
  · intro hd
    exact covBy_of_dim_eq_add_one dA ((genericPoint_spec A).specializes trivial) (by omega)

variable (sA : A ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sA]
  (sB : B ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sB]
  (dA : DimensionFunction A) (dB : DimensionFunction B) (u : A ⟶ B) [IsProper u] [IsDominant u]

include sA sB in
/-- **Lemma Dim-1 (i).**  Let `u : A ⟶ B` be a proper dominant morphism of integral schemes
locally of finite type over a field, whose generic points have the same dimension.  A point lying
over a point of coheight one has coheight one. -/
theorem coheight_eq_one_of_coheight_apply_eq_one
    (hd : dA (genericPoint A) = dB (genericPoint B)) (x : A)
    (hx : coheight (u.base x) = 1) : coheight x = 1 := by
  rw [coheight_eq_one_iff_dim_eq_genericPoint_sub_one sB dB] at hx
  rw [coheight_eq_one_iff_dim_eq_genericPoint_sub_one sA dA]
  have hle := DimensionFunction.apply_le_of_isProper dA dB u x
  have hne : genericPoint A ≠ x := by
    rintro rfl
    rw [Scheme.map_genericPoint_of_isDominant u] at hx
    omega
  have hlt := ProperPushforwardDivisor.dim_lt_of_specializes dA
    ((genericPoint_spec A).specializes trivial) hne
  omega

omit [IsProper u] [IsDominant u] in
include sA sB in
/-- **Lemma Dim-1 (ii).**  Under the hypotheses of `coheight_eq_one_of_coheight_apply_eq_one`,
at a point `x` of coheight one, the dimensions of `x` and `u x` agree exactly when `u x` has
coheight one (properness and dominance are not needed for this part). -/
theorem dim_eq_iff_coheight_apply_eq_one
    (hd : dA (genericPoint A) = dB (genericPoint B)) (x : A) (hx : coheight x = 1) :
    dA x = dB (u.base x) ↔ coheight (u.base x) = 1 := by
  rw [coheight_eq_one_iff_dim_eq_genericPoint_sub_one sA dA] at hx
  rw [coheight_eq_one_iff_dim_eq_genericPoint_sub_one sB dB]
  omega

end DimOne

/-! ## (G.1) A regular representative on an affine open -/

/-- **(G.1)** Every rational function on an integral scheme is the germ of a section over some
nonempty affine open. -/
theorem exists_affineOpen_germ_eq {V : Scheme.{u}} [IsIntegral V] (φ : V.functionField) :
    ∃ (U : V.Opens) (_ : IsAffineOpen U) (_ : Nonempty U) (φ₀ : Γ(V, U)),
      V.germToFunctionField U φ₀ = φ := by
  obtain ⟨U, hU, g, hg⟩ := V.presheaf.exists_germ_eq φ
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
    V.isBasis_affineOpens.exists_subset_of_mem_open hU U.isOpen
  have : Nonempty W := ⟨⟨_, hxW⟩⟩
  refine ⟨W, hW, this, V.presheaf.map (homOfLE hWU).op g, ?_⟩
  rw [← hg, ← V.presheaf.germ_res_apply (homOfLE hWU) (genericPoint V) hxW g]
  rfl

/-! ## Auxiliary facts on function fields, residue fields and dimensions -/

section Aux

/-- A morphism into an irreducible scheme sending some point to the generic point is
dominant. -/
theorem isDominant_of_apply_eq_genericPoint {X Y : Scheme.{u}} [IrreducibleSpace Y]
    (f : X ⟶ Y) {x : X} (hx : f.base x = genericPoint Y) : IsDominant f := by
  refine ⟨fun y ↦ ?_⟩
  exact ((genericPoint_spec Y).specializes trivial : genericPoint Y ⤳ y).mem_closed
    isClosed_closure (subset_closure ⟨x, hx⟩)

/-- The transport of a germ along the canonical identification of the stalks at two equal
points. -/
private lemma eqToHom_germ_apply' {Y : Scheme.{u}} {a b : Y} (e : b = a) (U : Y.Opens)
    (ha : a ∈ U) (hb : b ∈ U) (σ : Γ(Y, U)) :
    (eqToHom (congrArg (fun z => Y.presheaf.stalk z) e.symm) :
        Y.presheaf.stalk a ⟶ Y.presheaf.stalk b).hom (Y.presheaf.germ U a ha σ) =
      Y.presheaf.germ U b hb σ := by
  subst e
  simp

/-- The generic point of an irreducible scheme lies in every nonempty open. -/
theorem genericPoint_mem_of_nonempty {X : Scheme.{u}} [IrreducibleSpace X] (W : X.Opens)
    [h : Nonempty W] : genericPoint X ∈ W :=
  ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr (by simpa using h)

/-- **Function-field pullback of a germ.**  For a dominant morphism `f : X ⟶ Y` of integral
schemes, a section `σ` of `Y` over a nonempty open `W`, and a nonempty open `W' ⊆ f⁻¹ W`, the
pullback of the rational function `σ` is the rational function `f^* σ |_{W'}`. -/
theorem dominantFunctionFieldMap_germToFunctionField {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) [IsDominant f] (W : Y.Opens) [Nonempty W] (W' : X.Opens)
    [Nonempty W'] (hle : W' ≤ f ⁻¹ᵁ W) (σ : Γ(Y, W)) :
    Scheme.dominantFunctionFieldMap f (Y.germToFunctionField W σ) =
      X.germToFunctionField W' ((f.appLE W W' hle).hom σ) := by
  have e : f.base (genericPoint X) = genericPoint Y := Scheme.map_genericPoint_of_isDominant f
  have hgW' : genericPoint X ∈ W' := genericPoint_mem_of_nonempty W'
  have he : f.base (genericPoint X) ∈ W := hle hgW'
  change (f.stalkMap (genericPoint X)).hom
    ((eqToHom (congrArg (fun z => Y.presheaf.stalk z) e.symm)).hom
      (Y.presheaf.germ W (genericPoint Y) (genericPoint_mem_of_nonempty W) σ)) = _
  rw [eqToHom_germ_apply' e W _ he σ, Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE,
    CommRingCat.comp_apply]
  exact (X.presheaf.germ_res_apply (homOfLE hle) _ hgW' _).symm

/-- `appLE` from the whole space to the whole space is `appTop`. -/
theorem appLE_top_top_eq_appTop {X Y : Scheme.{u}} (f : X ⟶ Y) (e : ⊤ ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ e = f.appTop := by
  rw [Scheme.Hom.appLE, show homOfLE e = 𝟙 _ from Subsingleton.elim _ _]
  simp

/-- The residue transcendence degree is invariant under a morphism whose residue field map at
the point is bijective (e.g. an open or closed immersion, or a birational map at the generic
point). -/
theorem resTrdeg_comp_of_bijective {k : Type u} [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ X) (y : Y)
    (hg : Function.Bijective (g.residueFieldMap y).hom) :
    FiniteTypeDimension.resTrdeg (g ≫ f) y = FiniteTypeDimension.resTrdeg f (g.base y) :=
  (FiniteTypeDimension.trdegOf_congr _ _ (RingEquiv.ofBijective (g.residueFieldMap y).hom hg)
    fun c ↦ FiniteTypeDimension.residueFieldMap_residueMap f g y c).symm

/-- If `g ≫ p` has bijective residue field map at `y`, then so does `g`. -/
theorem residueFieldMap_bijective_of_comp {X Y Z : Scheme.{u}} (g : Y ⟶ X) (p : X ⟶ Z)
    (y : Y) (h : Function.Bijective ((g ≫ p).residueFieldMap y).hom) :
    Function.Bijective (g.residueFieldMap y).hom := by
  rw [Scheme.residueFieldMap_comp] at h
  refine ⟨RingHom.injective _, fun z ↦ ?_⟩
  obtain ⟨x, hx⟩ := h.2 z
  exact ⟨_, hx⟩

/-- **Transcendence passes from function fields to residue fields at the generic point.**  For a
dominant morphism `f : X ⟶ Y` of integral schemes and `s ∈ K(X)` transcendental over `K(Y)`
(through `f`), the value of `s` in `κ(η_X)` is transcendental over `κ(f η_X)`. -/
theorem transcendental_residue_genericPoint {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (s : X.functionField)
    (hs : letI := (Scheme.dominantFunctionFieldMap f).toAlgebra
      Transcendental Y.functionField s) :
    letI := (f.residueFieldMap (genericPoint X)).hom.toAlgebra
    Transcendental (Y.residueField (f.base (genericPoint X)))
      ((X.residue (genericPoint X)).hom s) := by
  let _ := (Scheme.dominantFunctionFieldMap f).toAlgebra
  let _ := (f.residueFieldMap (genericPoint X)).hom.toAlgebra
  let t : Y.functionField →+* Y.residueField (f.base (genericPoint X)) :=
    (Y.residue (f.base (genericPoint X))).hom.comp
      (eqToHom (congrArg (fun z ↦ Y.presheaf.stalk z)
        (Scheme.map_genericPoint_of_isDominant f).symm) :
        Y.presheaf.stalk (genericPoint Y) ⟶ Y.presheaf.stalk (f.base (genericPoint X))).hom
  have ht : Function.Surjective t :=
    (Y.residue_surjective _).comp (ConcreteCategory.bijective_of_isIso _).2
  let e : Y.functionField ≃+* Y.residueField (f.base (genericPoint X)) :=
    RingEquiv.ofBijective t ⟨RingHom.injective _, ht⟩
  refine (transcendental_ringHom_iff_of_comp_eq e (X.residue (genericPoint X)).hom
    (RingHom.injective _) ?_).2 hs
  ext a
  change (f.residueFieldMap (genericPoint X)).hom ((Y.residue _).hom _) =
    (X.residue (genericPoint X)).hom ((f.stalkMap (genericPoint X)).hom _)
  rw [← CommRingCat.comp_apply, Scheme.residue_residueFieldMap, CommRingCat.comp_apply]
  rfl

/-- **Transcendence degree lower bound.**  If the residue field `κ(x)` contains an element
transcendental over `κ(p x)`, then the residue transcendence degree jumps by at least one along
`p`. -/
theorem resTrdeg_add_one_le_of_transcendental {k : Type u} [Field k] {X Y : Scheme.{u}}
    (sY : Y ⟶ Spec (CommRingCat.of k)) (p : X ⟶ Y) (x : X) (c : X.residueField x)
    (hc : letI := (p.residueFieldMap x).hom.toAlgebra
      Transcendental (Y.residueField (p.base x)) c) :
    FiniteTypeDimension.resTrdeg sY (p.base x) + 1 ≤ FiniteTypeDimension.resTrdeg (p ≫ sY) x := by
  let _ : Algebra k (Y.residueField (p.base x)) :=
    (FiniteTypeDimension.residueMap sY (p.base x)).toAlgebra
  let _ : Algebra (Y.residueField (p.base x)) (X.residueField x) :=
    (p.residueFieldMap x).hom.toAlgebra
  let _ : Algebra k (X.residueField x) := (FiniteTypeDimension.residueMap (p ≫ sY) x).toAlgebra
  have : IsScalarTower k (Y.residueField (p.base x)) (X.residueField x) :=
    IsScalarTower.of_algebraMap_eq fun c ↦
      (FiniteTypeDimension.residueFieldMap_residueMap sY p x c).symm
  have : FaithfulSMul k (Y.residueField (p.base x)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective _)
  have : FaithfulSMul (Y.residueField (p.base x)) (X.residueField x) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective _)
  have : Algebra.Transcendental (Y.residueField (p.base x)) (X.residueField x) := ⟨⟨c, hc⟩⟩
  have hadd := trdeg_add_eq k (Y.residueField (p.base x)) (A := X.residueField x)
  have hpos := Cardinal.one_le_iff_pos.2
    (trdeg_pos (Y.residueField (p.base x)) (X.residueField x))
  rw [FiniteTypeDimension.resTrdeg, FiniteTypeDimension.resTrdeg,
    FiniteTypeDimension.trdegOf_eq (FiniteTypeDimension.residueMap sY (p.base x)) fun _ ↦ rfl,
    FiniteTypeDimension.trdegOf_eq (FiniteTypeDimension.residueMap (p ≫ sY) x) fun _ ↦ rfl,
    ← hadd, map_add]
  gcongr
  calc (1 : ℕ∞) = Cardinal.toENat 1 := (map_one _).symm
    _ ≤ _ := OrderHomClass.mono Cardinal.toENat hpos

/-- Principal cycles of powers. -/
theorem principalCycle_pow_graphClosure {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {x : X.functionField} (hx : x ≠ 0) (n : ℕ) :
    X.principalCycle (x ^ n) = n • X.principalCycle x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Scheme.principalCycle_mul (pow_ne_zero _ hx) hx, ih, succ_nsmul]

/-- **Pushforward of a principal divisor along an equidimensional proper dominant morphism out of
an integral closed subscheme** (over a field).  Let `Z ⊆ X` be an integral closed subscheme,
`u : Z ⟶ B` a proper dominant morphism to an integral scheme, both `X` and `B` locally of finite
type over `k`, and suppose the generic points of `Z` and `B` have the same dimension.  Then
`u_* div(ψ) = div(Nm ψ)`, with the weights on `Z` induced from `X`. -/
theorem map_principalCycle_of_dim_genericPoint_eq {k : Type u} [Field k] {X B : Scheme.{u}}
    [IsIntegral B] [IsLocallyNoetherian B] (Z : IntegralClosedSubscheme X)
    (sX : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sX] (dX : DimensionFunction X)
    (sB : B ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sB] (dB : DimensionFunction B)
    (u : Z.scheme ⟶ B) [IsProper u] [IsDominant u]
    [Algebra B.functionField Z.scheme.functionField]
    (halg : algebraMap B.functionField Z.scheme.functionField = Scheme.dominantFunctionFieldMap u)
    (hd : dX Z.genericPointImage = dB (genericPoint B)) (ψ : Z.scheme.functionField)
    (hψ : ψ ≠ 0) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map u (fun z ↦ dX (Z.inclusion.base z)) dB
        (Z.scheme.principalCycle ψ) =
      B.principalCycle (Algebra.norm B.functionField ψ) := by
  let dZ := FiniteTypeDimension.dimensionFunction (Z.inclusion ≫ sX)
  have hZ : ∀ z, dZ z = dX (Z.inclusion.base z) := fun z ↦
    DimensionFunction.apply_eq_of_isClosedImmersion dZ dX Z.inclusion z
  have hd' : dZ (genericPoint Z.scheme) = dB (genericPoint B) := by rw [hZ]; exact hd
  refine ProperPushforwardDivisor.map_principalCycle_eq_principalCycle_norm u halg _ _
    (coheight_eq_one_of_coheight_apply_eq_one (Z.inclusion ≫ sX) sB dZ dB u hd')
    (fun x hx ↦ ?_) ψ hψ
  rw [← hZ]
  exact dim_eq_iff_coheight_apply_eq_one (Z.inclusion ≫ sX) sB dZ dB u hd' x hx

end Aux

/-! ## (G.2) The graph of a regular function and its closure -/

section Graph

variable {V : Scheme.{u}} [IsIntegral V] [IsLocallyNoetherian V] (U : V.Opens) [Nonempty U]
  (φ₀ : Γ(V, U))

/-- The section `φ₀ ∈ Γ(V, U)`, as a global section of the open subscheme `U`. -/
noncomputable def graphCoord : Γ(U.toScheme, ⊤) :=
  (U.ι.appLE U ⊤ (by simp)).hom φ₀

/-- **The graph** `U ⟶ ℙ¹_V`, `u ↦ (u, φ₀(u))`: the point of the affine chart
`𝔸¹_V ⊆ ℙ¹_V` with coordinate `φ₀`, over the open immersion `U ⟶ V`. -/
noncomputable def graphMap : U.toScheme ⟶ P1.P1S V :=
  AffineSpace.homOfVector U.ι (fun _ ↦ graphCoord U φ₀) ≫ P1.affineChart 0 V

omit [IsIntegral V] [IsLocallyNoetherian V] [Nonempty U] in
/-- The graph lies over `U ⟶ V`. -/
@[reassoc (attr := simp)]
theorem graphMap_pr : graphMap U φ₀ ≫ P1.pr V = U.ι := by
  simp [graphMap]

variable [CompactSpace U]

/-- The graph is quasi-compact (its source is quasi-compact and `ℙ¹_V ⟶ V` is separated). -/
instance quasiCompact_graphMap : QuasiCompact (graphMap U φ₀) := by
  have : QuasiCompact (graphMap U φ₀ ≫ P1.pr V) := by
    rw [graphMap_pr]
    infer_instance
  exact QuasiCompact.of_comp _ (P1.pr V)

/-- **The graph closure** `Ṽ ⊆ ℙ¹_V`: the scheme-theoretic image of the graph of `φ₀`, an
integral closed subscheme. -/
noncomputable def graphClosure : IntegralClosedSubscheme (P1.P1S V) where
  scheme := (graphMap U φ₀).image
  inclusion := (graphMap U φ₀).imageι
  isIntegral :=
    have _h1 := _root_.AlgebraicGeometry.Scheme.isReduced_image (graphMap U φ₀)
    have _h2 := _root_.AlgebraicGeometry.Scheme.irreducibleSpace_image (graphMap U φ₀)
    isIntegral_of_irreducibleSpace_of_isReduced _
  isLocallyNoetherian := _root_.AlgebraicGeometry.Scheme.isLocallyNoetherian_image _

/-- The dominant morphism from `U` onto the graph closure. -/
noncomputable def toGraphClosure : U.toScheme ⟶ (graphClosure U φ₀).scheme :=
  (graphMap U φ₀).toImage

/-- `U ⟶ Ṽ ⟶ ℙ¹_V` is the graph. -/
@[reassoc (attr := simp)]
theorem toGraphClosure_inclusion :
    toGraphClosure U φ₀ ≫ (graphClosure U φ₀).inclusion = graphMap U φ₀ :=
  Scheme.Hom.toImage_imageι _

/-- `U ⟶ Ṽ` is dominant. -/
instance isDominant_toGraphClosure : IsDominant (toGraphClosure U φ₀) :=
  inferInstanceAs (IsDominant (graphMap U φ₀).toImage)

/-- The generic point of `U` maps to the generic point of the graph closure. -/
theorem toGraphClosure_genericPoint :
    (toGraphClosure U φ₀).base (genericPoint U.toScheme) =
      genericPoint (graphClosure U φ₀).scheme :=
  Scheme.map_genericPoint_of_isDominant _

/-- The generic point of the graph closure (as a point of `ℙ¹_V`) is the image of the generic
point of `U` under the graph. -/
theorem genericPointImage_graphClosure :
    (graphClosure U φ₀).genericPointImage = (graphMap U φ₀).base (genericPoint U.toScheme) := by
  change (graphClosure U φ₀).inclusion.base (genericPoint _) = _
  rw [← toGraphClosure_genericPoint, ← Scheme.Hom.comp_apply, toGraphClosure_inclusion]

/-! ## (G.3) The projection of the graph closure to `V` -/

/-- **The projection** `q : Ṽ ⟶ V`, the restriction of `ℙ¹_V ⟶ V` to the graph closure. -/
noncomputable def q : (graphClosure U φ₀).scheme ⟶ V :=
  (graphClosure U φ₀).inclusion ≫ P1.pr V

/-- `q` is proper. -/
instance isProper_q : IsProper (q U φ₀) := by
  unfold q
  infer_instance

/-- `U ⟶ Ṽ ⟶ V` is the open immersion `U ⟶ V`. -/
@[reassoc (attr := simp)]
theorem toGraphClosure_q : toGraphClosure U φ₀ ≫ q U φ₀ = U.ι := by
  simp [q]

/-- `q` maps the generic point of `Ṽ` to the generic point of `V`. -/
theorem q_genericPoint :
    (q U φ₀).base (genericPoint (graphClosure U φ₀).scheme) = genericPoint V := by
  rw [← toGraphClosure_genericPoint, ← Scheme.Hom.comp_apply, toGraphClosure_q]
  exact genericPoint_eq_of_isOpenImmersion U.ι

/-- `q` is dominant. -/
instance isDominant_q : IsDominant (q U φ₀) :=
  isDominant_of_apply_eq_genericPoint _ (q_genericPoint U φ₀)

/-- **(G.3)** `q` is birational: its function field map `K(V) → K(Ṽ)` is bijective. -/
theorem dominantFunctionFieldMap_q_bijective :
    Function.Bijective (Scheme.dominantFunctionFieldMap (q U φ₀)) := by
  have hcomp : (Scheme.dominantFunctionFieldMap (toGraphClosure U φ₀)).comp
      (Scheme.dominantFunctionFieldMap (q U φ₀)) = Scheme.dominantFunctionFieldMap U.ι := by
    rw [← dominantFunctionFieldMap_comp]
    exact dominantFunctionFieldMap_congr (toGraphClosure_q U φ₀)
  have hU := P1.dominantFunctionFieldMap_bijective_of_isOpenImmersion U.ι
  rw [← hcomp] at hU
  refine ⟨RingHom.injective _, fun y ↦ ?_⟩
  obtain ⟨x, hx⟩ := hU.2 (Scheme.dominantFunctionFieldMap (toGraphClosure U φ₀) y)
  exact ⟨x, (Scheme.dominantFunctionFieldMap (toGraphClosure U φ₀)).injective hx⟩

/-- The function field of the graph closure is an algebra over `K(V)` through `q`. -/
noncomputable instance algebraQ :
    Algebra V.functionField (graphClosure U φ₀).scheme.functionField :=
  (Scheme.dominantFunctionFieldMap (q U φ₀)).toAlgebra

/-- The algebra structure `K(V) → K(Ṽ)` is the function field map of `q`. -/
theorem algebraMap_q :
    algebraMap V.functionField (graphClosure U φ₀).scheme.functionField =
      Scheme.dominantFunctionFieldMap (q U φ₀) :=
  rfl

/-- `K(Ṽ) / K(V)` has degree one. -/
theorem finrank_functionField_q :
    Module.finrank V.functionField (graphClosure U φ₀).scheme.functionField = 1 := by
  let e : V.functionField ≃ₗ[V.functionField] (graphClosure U φ₀).scheme.functionField :=
    LinearEquiv.ofBijective (Algebra.linearMap _ _) (dominantFunctionFieldMap_q_bijective U φ₀)
  rw [← e.finrank_eq, Module.finrank_self]

/-- The norm along `q` of a function pulled back from `V` is the function itself. -/
theorem norm_algebraMap_q (x : V.functionField) :
    Algebra.norm V.functionField
      (algebraMap V.functionField (graphClosure U φ₀).scheme.functionField x) = x := by
  rw [Algebra.norm_algebraMap, finrank_functionField_q, pow_one]

/-- The rational function `φ̃ := q^* φ` on the graph closure, where `φ` is the germ of `φ₀`. -/
noncomputable def phiTilde : (graphClosure U φ₀).scheme.functionField :=
  algebraMap V.functionField _ (V.germToFunctionField U φ₀)

/-! ## (G.4) Dimensions along `q` -/

omit [IsLocallyNoetherian V] [CompactSpace U] in
/-- The residue field map of the graph at the generic point of `U` is bijective. -/
theorem residueFieldMap_graphMap_bijective :
    Function.Bijective ((graphMap U φ₀).residueFieldMap (genericPoint U.toScheme)).hom := by
  apply residueFieldMap_bijective_of_comp _ (P1.pr V)
  rw [graphMap_pr]
  exact ConcreteCategory.bijective_of_isIso _

/-- **(G.4)** The generic point of the graph closure has the dimension of the generic point of
`V`. -/
theorem dim_genericPoint_graphClosure {k : Type u} [Field k] (sV : V ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType sV] (dV : DimensionFunction V) (dP : DimensionFunction (P1.P1S V)) :
    dP (graphClosure U φ₀).genericPointImage = dV (genericPoint V) := by
  rw [dimensionFunction_eq_of_locallyOfFiniteType (P1.pr V ≫ sV) dP,
    dimensionFunction_eq_of_locallyOfFiniteType sV dV, genericPointImage_graphClosure,
    FiniteTypeDimension.dimensionFunction_apply, FiniteTypeDimension.dimensionFunction_apply,
    ← resTrdeg_comp_of_bijective _ _ _ (residueFieldMap_graphMap_bijective U φ₀),
    graphMap_pr_assoc, FiniteTypeDimension.resTrdeg_comp, genericPoint_eq_of_isOpenImmersion]

/-- `φ̃` is nonzero when `φ` is. -/
theorem phiTilde_ne_zero (hφ : V.germToFunctionField U φ₀ ≠ 0) : phiTilde U φ₀ ≠ 0 :=
  (map_ne_zero _).2 hφ

/-- **(G.4.1)** The pushforward along `q` of the divisor of `φ̃` is the divisor of `φ`. -/
theorem map_q_principalCycle {k : Type u} [Field k] (sV : V ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType sV] (dV : DimensionFunction V) (dP : DimensionFunction (P1.P1S V)) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map (q U φ₀)
        (fun z ↦ dP ((graphClosure U φ₀).inclusion.base z)) dV
        ((graphClosure U φ₀).scheme.principalCycle (phiTilde U φ₀)) =
      V.principalCycle (V.germToFunctionField U φ₀) := by
  by_cases hφ : V.germToFunctionField U φ₀ = 0
  · rw [phiTilde, hφ, map_zero, Scheme.principalCycle_zero, Scheme.principalCycle_zero,
      AlgebraicCycle.map_zero]
  rw [map_principalCycle_of_dim_genericPoint_eq (graphClosure U φ₀) (P1.pr V ≫ sV) dP sV dV
    (q U φ₀) (algebraMap_q U φ₀) (dim_genericPoint_graphClosure U φ₀ sV dV dP) _
    (phiTilde_ne_zero U φ₀ hφ), phiTilde, norm_algebraMap_q]

end Graph

/-! ## (G.5) The map from the graph closure to `ℙ¹` of the target -/

section ToP1

variable {V : Scheme.{u}} [IsIntegral V] [IsLocallyNoetherian V] (U : V.Opens) [Nonempty U]
  (φ₀ : Γ(V, U)) [CompactSpace U] {V' : Scheme.{u}} [IsIntegral V'] [IsLocallyNoetherian V']
  (h : V ⟶ V')

/-- **The map `g : Ṽ ⟶ ℙ¹_{V'}`**, the restriction of `ℙ¹_h : ℙ¹_V ⟶ ℙ¹_{V'}` to the graph
closure. -/
noncomputable def g : (graphClosure U φ₀).scheme ⟶ P1.P1S V' :=
  (graphClosure U φ₀).inclusion ≫ P1.P1S.map h

omit [IsIntegral V'] [IsLocallyNoetherian V'] in
/-- `g` lies over `h`: `g ≫ pr = q ≫ h`. -/
@[reassoc]
theorem g_pr : g U φ₀ h ≫ P1.pr V' = q U φ₀ ≫ h := by
  simp [g, q]

omit [IsIntegral V'] [IsLocallyNoetherian V'] in
/-- `g` is proper when `h` is. -/
instance isProper_g [IsProper h] : IsProper (g U φ₀ h) := by
  have : IsProper (g U φ₀ h ≫ P1.pr V') := by
    rw [g_pr]
    infer_instance
  exact IsProper.of_comp _ (P1.pr V')

/-- The graph of `φ₀` over `U ⟶ V ⟶ V'`, as a morphism to the affine line over `V'`. -/
noncomputable def graphVec : U.toScheme ⟶ 𝔸(PUnit; V') :=
  AffineSpace.homOfVector (U.ι ≫ h) (fun _ ↦ graphCoord U φ₀)

omit [IsIntegral V] [IsLocallyNoetherian V] [Nonempty U] [CompactSpace U] [IsIntegral V']
  [IsLocallyNoetherian V'] in
/-- `graphVec` lies over `U ⟶ V'`. -/
@[reassoc (attr := simp)]
theorem graphVec_over : graphVec U φ₀ h ≫ 𝔸(PUnit; V') ↘ V' = U.ι ≫ h :=
  AffineSpace.homOfVector_over _ _

omit [IsIntegral V] [IsLocallyNoetherian V] [Nonempty U] [CompactSpace U] [IsIntegral V']
  [IsLocallyNoetherian V'] in
/-- Naturality of the graph: `U ⟶ ℙ¹_V ⟶ ℙ¹_{V'}` is `graphVec` followed by the chart. -/
theorem graphMap_map : graphMap U φ₀ ≫ P1.P1S.map h = graphVec U φ₀ h ≫ P1.affineChart 0 V' := by
  have hv : AffineSpace.homOfVector U.ι (fun _ ↦ graphCoord U φ₀) ≫ AffineSpace.map PUnit h =
      graphVec U φ₀ h := by
    ext1
    · simp [graphVec]
    · simp [graphVec]
  rw [graphMap, Category.assoc, P1.affineChart_map, ← Category.assoc, hv]

omit [IsIntegral V'] [IsLocallyNoetherian V'] in
/-- `U ⟶ Ṽ ⟶ ℙ¹_{V'}` is `graphVec` followed by the chart. -/
theorem toGraphClosure_g :
    toGraphClosure U φ₀ ≫ g U φ₀ h = graphVec U φ₀ h ≫ P1.affineChart 0 V' := by
  rw [g, toGraphClosure_inclusion_assoc, graphMap_map]

variable [IsDominant h] [Algebra V'.functionField V.functionField]
  (halg : algebraMap V'.functionField V.functionField = Scheme.dominantFunctionFieldMap h)

omit [IsLocallyNoetherian V] [CompactSpace U] [IsLocallyNoetherian V'] in
include halg in
/-- **The key transcendence step of (G.5).**  If `φ` is transcendental over `K(V')`, the graph
`U ⟶ 𝔸¹_{V'}` of `φ₀` maps the generic point of `U` to the generic point of `𝔸¹_{V'}`: its
image point has residue field containing the transcendental element `φ`, which forces its
dimension to be maximal (`P1.dimensionFunction_genericPoint_affineSpace`). -/
theorem graphVec_genericPoint {k : Type u} [Field k] (sV' : V' ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType sV'] (hφ : Transcendental V'.functionField (V.germToFunctionField U φ₀)) :
    (graphVec U φ₀ h).base (genericPoint U.toScheme) = genericPoint 𝔸(PUnit; V') := by
  set w := graphVec U φ₀ h with hw_def
  set π := 𝔸(PUnit; V') ↘ V' with hπ_def
  set x₀ := genericPoint U.toScheme with hx₀_def
  have hwπ : w ≫ π = U.ι ≫ h := graphVec_over U φ₀ h
  have : IsDominant (w ≫ π) := by rw [hwπ]; infer_instance
  -- `φ`, read on `U`, is transcendental over `K(V')` through `w ≫ π = U.ι ≫ h`.
  have hU : Scheme.dominantFunctionFieldMap U.ι (V.germToFunctionField U φ₀) =
      U.toScheme.germToFunctionField ⊤ (graphCoord U φ₀) :=
    dominantFunctionFieldMap_germToFunctionField U.ι U ⊤ (by simp) φ₀
  have hs : letI := (Scheme.dominantFunctionFieldMap (w ≫ π)).toAlgebra
      Transcendental V'.functionField (U.toScheme.germToFunctionField ⊤ (graphCoord U φ₀)) := by
    let _ := (Scheme.dominantFunctionFieldMap (w ≫ π)).toAlgebra
    rw [← hU]
    refine (transcendental_ringHom_iff_of_comp_eq (RingEquiv.refl V'.functionField)
      (Scheme.dominantFunctionFieldMap U.ι) (RingHom.injective _) ?_).2 hφ
    ext a
    change Scheme.dominantFunctionFieldMap (w ≫ π) a =
      Scheme.dominantFunctionFieldMap U.ι (algebraMap V'.functionField V.functionField a)
    rw [halg, dominantFunctionFieldMap_congr hwπ, dominantFunctionFieldMap_comp]
    rfl
  have hres := transcendental_residue_genericPoint (w ≫ π) _ hs
  -- The coordinate of `𝔸¹` at the image point is transcendental over the base.
  let c : 𝔸(PUnit; V').residueField (w.base x₀) :=
    (𝔸(PUnit; V').Γevaluation (w.base x₀)).hom (AffineSpace.coord V' PUnit.unit)
  have hwc : (w.residueFieldMap x₀).hom c = (U.toScheme.residue x₀).hom
      (U.toScheme.germToFunctionField ⊤ (graphCoord U φ₀)) := by
    simp only [c, Scheme.Γevaluation_naturality_apply]
    rw [hw_def, graphVec, AffineSpace.homOfVector_appTop_coord]
    rfl
  have hc : letI := (π.residueFieldMap (w.base x₀)).hom.toAlgebra
      Transcendental (V'.residueField (π.base (w.base x₀))) c := by
    let _ := (π.residueFieldMap (w.base x₀)).hom.toAlgebra
    let _ : Algebra (V'.residueField (π.base (w.base x₀))) (U.toScheme.residueField x₀) :=
      ((w ≫ π).residueFieldMap x₀).hom.toAlgebra
    intro halgc
    apply hres
    have key := IsAlgebraic.ringHom_of_comp_eq (RingHom.id _) (w.residueFieldMap x₀).hom
      halgc (fun _ _ h ↦ h) (by
        ext a
        change ((w ≫ π).residueFieldMap x₀).hom a =
          (w.residueFieldMap x₀).hom ((π.residueFieldMap (w.base x₀)).hom a)
        rw [Scheme.residueFieldMap_comp]
        rfl)
    rw [hwc] at key
    exact key
  have hlow := resTrdeg_add_one_le_of_transcendental sV' π (w.base x₀) c hc
  have hπζ : π.base (w.base x₀) = genericPoint V' := by
    rw [← Scheme.Hom.comp_apply, hwπ, Scheme.Hom.comp_apply, genericPoint_eq_of_isOpenImmersion,
      Scheme.map_genericPoint_of_isDominant]
  rw [hπζ] at hlow
  -- The upper bound: the generic point of `𝔸¹_{V'}` has dimension `dim V' + 1`.
  have hP8 := P1.dimensionFunction_genericPoint_affineSpace V' sV'
  by_contra hne
  have hlt := ProperPushforwardDivisor.dim_lt_of_specializes
    (FiniteTypeDimension.dimensionFunction (π ≫ sV'))
    ((genericPoint_spec 𝔸(PUnit; V')).specializes trivial : genericPoint 𝔸(PUnit; V') ⤳ _)
    (Ne.symm hne)
  rw [hP8] at hlt
  simp only [FiniteTypeDimension.dimensionFunction_apply] at hlt
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 (FiniteTypeDimension.resTrdeg_ne_top sV'
    (genericPoint V'))
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1 (FiniteTypeDimension.resTrdeg_ne_top (π ≫ sV')
    (w.base x₀))
  rw [← ha, ← hb] at hlow
  rw [← ha, ← hb] at hlt
  have hlow' : a + 1 ≤ b := by exact_mod_cast hlow
  simp only [ENat.toNat_natCast] at hlt
  omega

omit [IsLocallyNoetherian V'] in
include halg in
/-- **(G.5)** If `φ` is transcendental over `K(V')`, then `g` maps the generic point of the graph
closure to the generic point of `ℙ¹_{V'}`. -/
theorem g_genericPoint {k : Type u} [Field k] (sV' : V' ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType sV'] (hφ : Transcendental V'.functionField (V.germToFunctionField U φ₀)) :
    (g U φ₀ h).base (genericPoint (graphClosure U φ₀).scheme) = genericPoint (P1.P1S V') := by
  rw [← toGraphClosure_genericPoint, ← Scheme.Hom.comp_apply, toGraphClosure_g,
    Scheme.Hom.comp_apply, graphVec_genericPoint U φ₀ h halg sV' hφ, P1.affineChart_genericPoint]

omit [IsLocallyNoetherian V'] in
include halg in
/-- **(G.5)** If `φ` is transcendental over `K(V')`, then `g` is dominant. -/
theorem isDominant_g {k : Type u} [Field k] (sV' : V' ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType sV'] (hφ : Transcendental V'.functionField (V.germToFunctionField U φ₀)) :
    IsDominant (g U φ₀ h) :=
  isDominant_of_apply_eq_genericPoint _ (g_genericPoint U φ₀ h halg sV' hφ)

omit [IsLocallyNoetherian V'] [Algebra V'.functionField V.functionField] in
/-- **(G.5)** If `dim V' = dim V - 1`, the generic point of `ℙ¹_{V'}` has the dimension of the
generic point of the graph closure. -/
theorem dim_genericPoint_eq_g {k : Type u} [Field k] (sV : V ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType sV] (sV' : V' ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sV']
    (dV : DimensionFunction V) (dV' : DimensionFunction V') (dP : DimensionFunction (P1.P1S V))
    (dT : DimensionFunction (P1.P1S V'))
    (hdim : dV' (genericPoint V') = dV (genericPoint V) - 1) :
    dT (genericPoint (P1.P1S V')) = dP (graphClosure U φ₀).genericPointImage := by
  rw [dim_genericPoint_graphClosure U φ₀ sV dV dP, ← P1.affineChart_genericPoint,
    dimensionFunction_eq_of_locallyOfFiniteType (P1.pr V' ≫ sV') dT,
    ← FiniteTypeDimension.dimensionFunction_comp (P1.pr V' ≫ sV') (P1.affineChart 0 V'),
    ProperPushforwardDivisor.dimensionFunction_eq
      (FiniteTypeDimension.dimensionFunction (P1.affineChart 0 V' ≫ P1.pr V' ≫ sV'))
      (FiniteTypeDimension.dimensionFunction (𝔸(PUnit; V') ↘ V' ≫ sV')),
    P1.dimensionFunction_genericPoint_affineSpace,
    ← dimensionFunction_eq_of_locallyOfFiniteType sV' dV']
  omega

omit [IsLocallyNoetherian V'] in
include halg in
/-- **(G.6)** The coordinate function of `ℙ¹_{V'}` pulls back along `g` to `φ̃`. -/
theorem dominantFunctionFieldMap_g_coordFn {k : Type u} [Field k]
    (sV' : V' ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sV']
    (hφ : Transcendental V'.functionField (V.germToFunctionField U φ₀))
    [IsDominant (g U φ₀ h)] :
    Scheme.dominantFunctionFieldMap (g U φ₀ h) (P1.coordFn V') = phiTilde U φ₀ := by
  have : IsDominant (graphVec U φ₀ h) :=
    isDominant_of_apply_eq_genericPoint _ (graphVec_genericPoint U φ₀ h halg sV' hφ)
  apply (Scheme.dominantFunctionFieldMap (toGraphClosure U φ₀)).injective
  have h1 : Scheme.dominantFunctionFieldMap (toGraphClosure U φ₀)
      (Scheme.dominantFunctionFieldMap (g U φ₀ h) (P1.coordFn V')) =
      Scheme.dominantFunctionFieldMap (graphVec U φ₀ h)
        (Scheme.dominantFunctionFieldMap (P1.affineChart 0 V') (P1.coordFn V')) := by
    rw [← RingHom.comp_apply, ← dominantFunctionFieldMap_comp,
      dominantFunctionFieldMap_congr (toGraphClosure_g U φ₀ h), dominantFunctionFieldMap_comp,
      RingHom.comp_apply]
  have h2 : Scheme.dominantFunctionFieldMap (toGraphClosure U φ₀) (phiTilde U φ₀) =
      Scheme.dominantFunctionFieldMap U.ι (V.germToFunctionField U φ₀) := by
    rw [phiTilde, algebraMap_q, ← RingHom.comp_apply, ← dominantFunctionFieldMap_comp,
      dominantFunctionFieldMap_congr (toGraphClosure_q U φ₀)]
  rw [h1, h2, P1.dominantFunctionFieldMap_affineChart_coordFn,
    dominantFunctionFieldMap_germToFunctionField _ ⊤ ⊤ (by simp),
    dominantFunctionFieldMap_germToFunctionField U.ι U ⊤ (by simp)]
  rw [appLE_top_top_eq_appTop, graphVec, AffineSpace.homOfVector_appTop_coord]
  rfl

omit [IsLocallyNoetherian V'] in
include halg in
/-- **(G.6)** With `K(Ṽ)` a `K(ℙ¹_{V'})`-algebra through `g`, the coordinate function maps to
`φ̃`. -/
theorem algebraMap_coordFn_eq {k : Type u} [Field k]
    (sV' : V' ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sV']
    (hφ : Transcendental V'.functionField (V.germToFunctionField U φ₀))
    [IsDominant (g U φ₀ h)]
    [Algebra (P1.P1S V').functionField (graphClosure U φ₀).scheme.functionField]
    (halgG : algebraMap (P1.P1S V').functionField (graphClosure U φ₀).scheme.functionField =
      Scheme.dominantFunctionFieldMap (g U φ₀ h)) :
    algebraMap (P1.P1S V').functionField (graphClosure U φ₀).scheme.functionField
      (P1.coordFn V') = phiTilde U φ₀ := by
  rw [halgG]
  exact dominantFunctionFieldMap_g_coordFn U φ₀ h halg sV' hφ

omit [IsLocallyNoetherian V'] in
include halg in
/-- **(G.6)** The norm of `φ̃` along `g` is a power of the coordinate function. -/
theorem norm_phi_tilde {k : Type u} [Field k]
    (sV' : V' ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sV']
    (hφ : Transcendental V'.functionField (V.germToFunctionField U φ₀))
    [IsDominant (g U φ₀ h)]
    [Algebra (P1.P1S V').functionField (graphClosure U φ₀).scheme.functionField]
    (halgG : algebraMap (P1.P1S V').functionField (graphClosure U φ₀).scheme.functionField =
      Scheme.dominantFunctionFieldMap (g U φ₀ h)) :
    Algebra.norm (P1.P1S V').functionField (phiTilde U φ₀) =
      P1.coordFn V' ^ Module.finrank (P1.P1S V').functionField
        (graphClosure U φ₀).scheme.functionField := by
  rw [← algebraMap_coordFn_eq U φ₀ h halg sV' hφ halgG, Algebra.norm_algebraMap]

include halg in
/-- **(G.6.1)** If `φ` is transcendental over `K(V')` and `dim V' = dim V - 1`, the pushforward
along `g` of the divisor of `φ̃` is `d · div(t)`, where `t` is the coordinate function of
`ℙ¹_{V'}` and `d = [K(Ṽ) : K(ℙ¹_{V'})]` (`0` if the extension is infinite). -/
theorem map_g_principalCycle {k : Type u} [Field k] (sV : V ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType sV] (sV' : V' ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType sV']
    [IsProper h] (dV : DimensionFunction V) (dV' : DimensionFunction V')
    (dP : DimensionFunction (P1.P1S V)) (dT : DimensionFunction (P1.P1S V'))
    (hdim : dV' (genericPoint V') = dV (genericPoint V) - 1)
    (hφ : Transcendental V'.functionField (V.germToFunctionField U φ₀))
    [IsDominant (g U φ₀ h)]
    [Algebra (P1.P1S V').functionField (graphClosure U φ₀).scheme.functionField]
    (halgG : algebraMap (P1.P1S V').functionField (graphClosure U φ₀).scheme.functionField =
      Scheme.dominantFunctionFieldMap (g U φ₀ h)) :
    _root_.AlgebraicGeometry.AlgebraicCycle.map (g U φ₀ h)
        (fun z ↦ dP ((graphClosure U φ₀).inclusion.base z)) dT
        ((graphClosure U φ₀).scheme.principalCycle (phiTilde U φ₀)) =
      Module.finrank (P1.P1S V').functionField (graphClosure U φ₀).scheme.functionField •
        (P1.P1S V').principalCycle (P1.coordFn V') := by
  have hφ0 : V.germToFunctionField U φ₀ ≠ 0 := fun h0 ↦ hφ (h0 ▸ isAlgebraic_zero)
  rw [map_principalCycle_of_dim_genericPoint_eq (graphClosure U φ₀) (P1.pr V ≫ sV) dP
    (P1.pr V' ≫ sV') dT (g U φ₀ h) halgG
    (dim_genericPoint_eq_g U φ₀ sV sV' dV dV' dP dT hdim).symm _ (phiTilde_ne_zero U φ₀ hφ0),
    norm_phi_tilde U φ₀ h halg sV' hφ halgG,
    principalCycle_pow_graphClosure (P1.coordFn_ne_zero V')]

end ToP1

end GraphClosure

end GromovWitten.AlgebraicGeometry.IntersectionTheory
