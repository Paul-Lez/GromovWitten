/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.IntersectionTheory.HomogeneityLocal
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundlePullbackFundamental
import GromovWitten.Algebra.FiniteTypeKrullDimension
import GromovWitten.Algebra.FiniteTypeDimensionFormula
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Dimension functions for schemes locally of finite type over a field

A `DimensionFunction X` (`IntersectionTheory/ChowGroup.lean`) certifies that the integer attached
to a point of `X` is the dimension of the closure of that point, i.e. its order-theoretic height
in the specialisation order.  Nothing in the repository constructs such a function, and none of
the restriction statements about graded cycles can discharge their compatibility hypothesis
`hdim : ∀ y, dimensionY y = dimensionX (g.base y)` for an open immersion `g`, because the height
of a point really can drop in an open subscheme (for instance on the spectrum of a discrete
valuation ring).

This file constructs the dimension function of a scheme `X` equipped with a structure morphism
`f : X ⟶ Spec k` to a field which is locally of finite type, and proves the compatibility with
*every* open immersion.  The key invariant is the transcendence degree of the residue field:

`FiniteTypeDimension.resTrdeg f x = trdeg k (κ(x))`,

which is manifestly unchanged by an open immersion because open immersions induce isomorphisms of
residue fields.  On an affine scheme `Spec A` with `A` a finitely generated `k`-algebra it computes
the height by `GromovWitten.Algebra.PrimeSpectrum.coheight_eq_toENat_trdeg_residueField`, and the
general case follows because every chain of specialisations ending at `x` lies in a single affine
open (an open subset is stable under generalisation).

## Main results

* `FiniteTypeDimension.resTrdeg_comp`: the residue transcendence degree is invariant under open
  immersions.
* `FiniteTypeDimension.resTrdeg_spec`: the affine dimension formula
  `resTrdeg h q = Order.height q` for `h : Spec A ⟶ Spec k` of finite type.
* `FiniteTypeDimension.height_eq_resTrdeg`: the global dimension formula
  `Order.height x = resTrdeg f x`.
* `FiniteTypeDimension.dimensionFunction f : DimensionFunction X` and
  `FiniteTypeDimension.dimensionFunction_comp`, the compatibility with open immersions, which is
  exactly the hypothesis `hdim` carried by every restriction statement of the repository.
* `FiniteTypeDimension.hasUniversalDimensionFormula_sections` and
  `FiniteTypeDimension.principalDivisorsHomogeneous`: homogeneity of principal divisors for the
  canonical dimension function, with no hypotheses beyond `LocallyOfFiniteType f`.
* `FiniteTypeDimension.locallyOfFiniteType_proj`,
  `FiniteTypeDimension.dimensionFunction_bundlePoint`,
  `FiniteTypeDimension.principalDivisorsHomogeneous_totalSpace` and
  `FiniteTypeDimension.flatPullbackBundleFiniteType`: the total space of a
  `VectorBundleTotalSpace.BundleData X ι` of finite rank is again locally of finite type over `k`,
  its canonical dimension function satisfies the shift `dim (bundlePoint 𝓔 x) = dim x + rank`, and
  the graded flat pullback of `BundlePullbackGlobal.flatPullbackBundleGlobal` becomes
  hypothesis-free.

All statements are unconditional: the only assumptions are `[Field k]` and `[LocallyOfFiniteType
f]` (plus `[Finite ι]` for the bundle statements).
-/

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

universe u v

namespace GromovWitten.AlgebraicGeometry.IntersectionTheory.FiniteTypeDimension

variable {k : Type u} [Field k]

/-! ## Transcendence degree along a ring homomorphism -/

section TrdegOf

/-- The transcendence degree, as an element of `ℕ∞`, of a field `K` over `k` along an explicitly
given ring homomorphism `φ : k →+* K`.  This wrapper avoids carrying `Algebra` instances that
depend on a scheme morphism. -/
noncomputable def trdegOf {K : Type u} [Field K] (φ : k →+* K) : ℕ∞ :=
  Cardinal.toENat (@Algebra.trdeg k K _ _ φ.toAlgebra)

/-- `trdegOf` computed from an ambient algebra structure. -/
theorem trdegOf_eq {K : Type u} [Field K] [inst : Algebra k K] (φ : k →+* K)
    (hφ : ∀ c, φ c = algebraMap k K c) :
    trdegOf φ = Cardinal.toENat (Algebra.trdeg k K) := by
  have h : φ.toAlgebra = inst := Algebra.algebra_ext _ _ fun c ↦ by
    simpa [RingHom.algebraMap_toAlgebra] using hφ c
  rw [trdegOf, h]

/-- Transcendence degree is invariant under a ring isomorphism compatible with the two
structure homomorphisms. -/
theorem trdegOf_congr {K L : Type u} [Field K] [Field L] (φ : k →+* K) (ψ : k →+* L)
    (e : K ≃+* L) (he : ∀ c, e (φ c) = ψ c) : trdegOf φ = trdegOf ψ := by
  let _ : Algebra k K := φ.toAlgebra
  let _ : Algebra k L := ψ.toAlgebra
  have hcomm : ∀ c, e (algebraMap k K c) = algebraMap k L c := he
  let e' : K ≃ₐ[k] L := { e with commutes' := hcomm }
  exact congrArg Cardinal.toENat e'.trdeg_eq

end TrdegOf

/-! ## The structure maps induced by a morphism to `Spec k` -/

section StructureMap

variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- The ring homomorphism `k → Γ(X, U)` induced by a structure morphism `f : X ⟶ Spec k`. -/
noncomputable def structureMap (U : X.Opens) : k →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ U (by simp)).hom

/-- The ring homomorphism `k → κ(x)` into the residue field at `x` induced by a structure
morphism `f : X ⟶ Spec k`. -/
noncomputable def residueMap (x : X) : k →+* X.residueField x :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom

/-- Evaluating a constant at a point of `U` gives the corresponding constant in the residue
field. -/
theorem evaluation_structureMap (U : X.Opens) (x : X) (hx : x ∈ U) (c : k) :
    X.evaluation U x hx (structureMap f U c) = residueMap f x c := by
  have h : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ U (by simp)) ≫
      X.evaluation U x hx =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop ≫ X.Γevaluation x := by
    simp only [Scheme.Hom.appLE, Scheme.Γevaluation, Scheme.evaluation, Category.assoc]
    rw [← Category.assoc (X.presheaf.map _), X.presheaf.germ_res]
    rfl
  exact congrArg (fun φ : CommRingCat.of k ⟶ X.residueField x ↦ φ.hom c) h

/-- The `k`-algebra structure on the sections of `X` over `U` induced by a structure morphism
`f : X ⟶ Spec k`. -/
@[instance_reducible]
noncomputable def sectionsAlgebra (U : X.Opens) : Algebra k Γ(X, U) :=
  (structureMap f U).toAlgebra

/-- For a morphism locally of finite type, the sections over an affine open form a finitely
generated `k`-algebra. -/
theorem finiteType_structureMap [LocallyOfFiniteType f] (U : X.Opens) (hU : IsAffineOpen U) :
    (structureMap f U).FiniteType :=
  RingHom.finiteType_respectsIso.2 _
    ((Scheme.ΓSpecIso (CommRingCat.of k)).symm).commRingCatIsoToRingEquiv
    (f.finiteType_appLE (isAffineOpen_top _) hU (le_top : U ≤ f ⁻¹ᵁ ⊤))

/-- The universal dimension formula holds for the sections over any affine open of a scheme
locally of finite type over a field. -/
theorem hasUniversalDimensionFormula_sections [LocallyOfFiniteType f] (U : X.Opens)
    (hU : IsAffineOpen U) : VectorBundle.HasUniversalDimensionFormula Γ(X, U) :=
  @GromovWitten.Algebra.FiniteTypeDimensionFormula.hasUniversalDimensionFormula_of_finiteType
    k _ Γ(X, U) _ (sectionsAlgebra f U) (finiteType_structureMap f U hU)

/-! ## The residue transcendence degree -/

/-- The transcendence degree over `k` of the residue field of `X` at `x`, as an element of
`ℕ∞`. -/
noncomputable def resTrdeg (x : X) : ℕ∞ := trdegOf (residueMap f x)

/-- The residue field maps of a morphism of schemes are `k`-algebra maps. -/
theorem residueFieldMap_residueMap {Y : Scheme.{u}} (g : Y ⟶ X) (y : Y) (c : k) :
    g.residueFieldMap y (residueMap f (g.base y) c) = residueMap (g ≫ f) y c := by
  have h : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop ≫
        X.Γevaluation (g.base y)) ≫ g.residueFieldMap y =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (g ≫ f).appTop ≫ Y.Γevaluation y := by
    rw [AlgebraicGeometry.Scheme.Hom.comp_appTop]
    simp only [Category.assoc]
    rw [Scheme.Γevaluation_naturality]
  exact congrArg (fun φ : CommRingCat.of k ⟶ Y.residueField y ↦ φ.hom c) h

/-- The residue transcendence degree is invariant under open immersions. -/
theorem resTrdeg_comp {Y : Scheme.{u}} (g : Y ⟶ X) [AlgebraicGeometry.IsOpenImmersion g]
    (y : Y) : resTrdeg (g ≫ f) y = resTrdeg f (g.base y) :=
  (trdegOf_congr _ _ (asIso (g.residueFieldMap y)).commRingCatIsoToRingEquiv
    fun c ↦ residueFieldMap_residueMap f g y c).symm

/-! ## The affine case -/

section Affine

variable {A : Type u} [CommRing A]

/-- The ring homomorphism `k → A` corresponding to a morphism `Spec A ⟶ Spec k`. -/
noncomputable def specAlgebraMap (h : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k)) :
    k →+* A :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ h.appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom

/-- `specAlgebraMap` is the global structure map read through the canonical isomorphism
`Γ(Spec A, ⊤) ≅ A`. -/
theorem specAlgebraMap_eq (h : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k)) :
    specAlgebraMap h = ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom).comp
      (structureMap h ⊤) := by
  simp only [specAlgebraMap, structureMap, Scheme.Hom.appLE]
  rfl

/-- The ring map `k → A` attached to a morphism locally of finite type is of finite type. -/
theorem finiteType_specAlgebraMap (h : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType h] : (specAlgebraMap h).FiniteType := by
  rw [specAlgebraMap_eq]
  exact RingHom.finiteType_respectsIso.1 _
    (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
    (finiteType_structureMap h ⊤ (isAffineOpen_top _))

/-- The ideal of a point of `Spec A`, viewed through the carrier of the scheme, is prime.  The
Mathlib instance is not found because the carrier of `Spec A` is only definitionally
`PrimeSpectrum A`. -/
instance isPrime_asIdeal (q : ↥(Spec (CommRingCat.of A))) : q.asIdeal.IsPrime :=
  PrimeSpectrum.isPrime (q : PrimeSpectrum A)

/-- The canonical isomorphism between the residue field of `Spec A` at `q` and the residue field
of the corresponding prime is compatible with the structure maps from `k`. -/
theorem residueFieldIso_residueMap (h : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k))
    (q : ↥(Spec (CommRingCat.of A))) (c : k) :
    (AlgebraicGeometry.Scheme.Spec.residueFieldIso (CommRingCat.of A) q).hom
        (residueMap h q c) =
      algebraMap A q.asIdeal.ResidueField (specAlgebraMap h c) := by
  have e0 := AlgebraicGeometry.Scheme.Spec.algebraMap_residueFieldIso_inv (CommRingCat.of A) q
  have e1 : (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫
      CommRingCat.ofHom (algebraMap A q.asIdeal.ResidueField) ≫
      (AlgebraicGeometry.Scheme.Spec.residueFieldIso (CommRingCat.of A) q).inv =
      (Spec (CommRingCat.of A)).Γevaluation q := by
    rw [e0, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rfl
  have key : (Spec (CommRingCat.of A)).Γevaluation q ≫
      (AlgebraicGeometry.Scheme.Spec.residueFieldIso (CommRingCat.of A) q).hom =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫
        CommRingCat.ofHom (algebraMap A q.asIdeal.ResidueField) := by
    rw [← e1]
    simp
  have hmor : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ h.appTop ≫
        (Spec (CommRingCat.of A)).Γevaluation q) ≫
      (AlgebraicGeometry.Scheme.Spec.residueFieldIso (CommRingCat.of A) q).hom =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ h.appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫
          CommRingCat.ofHom (algebraMap A q.asIdeal.ResidueField) := by
    rw [Category.assoc, Category.assoc, key]
  exact congrArg (fun φ : CommRingCat.of k ⟶
    CommRingCat.of q.asIdeal.ResidueField ↦ φ.hom c) hmor

/-- **The affine dimension formula.**  For a morphism `Spec A ⟶ Spec k` whose associated ring map
is of finite type, the residue transcendence degree at a point is the order-theoretic height of
that point, i.e. the dimension of its closure. -/
theorem resTrdeg_spec (h : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k))
    (hft : (specAlgebraMap h).FiniteType) (q : ↥(Spec (CommRingCat.of A))) :
    resTrdeg h q = Order.height q := by
  let _ : Algebra k A := (specAlgebraMap h).toAlgebra
  have _ : Algebra.FiniteType k A := hft
  have h1 := GromovWitten.Algebra.PrimeSpectrum.coheight_eq_toENat_trdeg_residueField
    (k := k) (A := A) q
  have h2 := VectorBundle.coheight_eq_height A q
  have h3 : resTrdeg h q = Cardinal.toENat (Algebra.trdeg k q.asIdeal.ResidueField) :=
    (trdegOf_congr (residueMap h q) (algebraMap k q.asIdeal.ResidueField)
      (AlgebraicGeometry.Scheme.Spec.residueFieldIso
        (CommRingCat.of A) q).commRingCatIsoToRingEquiv
      fun c ↦ (residueFieldIso_residueMap h q c).trans
        (IsScalarTower.algebraMap_apply k A _ c).symm).trans (trdegOf_eq _ fun _ ↦ rfl)
  rw [h3, ← h1, h2]

/-- Over a field, the coheight of a prime of a finitely generated algebra is finite. -/
theorem coheight_ne_top [Algebra k A] [Algebra.FiniteType k A] (p : PrimeSpectrum A) :
    Order.coheight p ≠ ⊤ := by
  have hprime : p.asIdeal.IsPrime := p.isPrime
  have hdom : IsDomain (A ⧸ p.asIdeal) := (Ideal.Quotient.isDomain_iff_prime _).mpr hprime
  have hft : Algebra.FiniteType k (A ⧸ p.asIdeal) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k p.asIdeal) Ideal.Quotient.mk_surjective
  have h1 := GromovWitten.Algebra.PrimeSpectrum.coheight_eq_ringKrullDim_quotient p
  have h2 := GromovWitten.Algebra.ringKrullDim_eq_toENat_trdeg k (A ⧸ p.asIdeal)
  have h3 : Algebra.trdeg k (A ⧸ p.asIdeal) < Cardinal.aleph0 :=
    _root_.trdeg_lt_aleph0_of_finiteType
  have h4 : Cardinal.toENat (Algebra.trdeg k (A ⧸ p.asIdeal)) ≠ ⊤ := fun hc ↦
    absurd (Cardinal.toENat_eq_top.1 hc) (not_le.2 h3)
  have h6 : Order.coheight p = Cardinal.toENat (Algebra.trdeg k (A ⧸ p.asIdeal)) := by
    exact_mod_cast h1.trans h2
  rw [h6]
  exact h4

/-- The residue transcendence degree on an affine scheme of finite type over a field is finite. -/
theorem resTrdeg_spec_ne_top (h : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of k))
    (hft : (specAlgebraMap h).FiniteType) (q : ↥(Spec (CommRingCat.of A))) :
    resTrdeg h q ≠ ⊤ := by
  let _ : Algebra k A := (specAlgebraMap h).toAlgebra
  have _ : Algebra.FiniteType k A := hft
  rw [resTrdeg_spec h hft q, ← VectorBundle.coheight_eq_height A q]
  exact coheight_ne_top (k := k) q

end Affine

end StructureMap

/-! ## The global dimension formula -/

section Global

/-- Open immersions are strictly monotone for the specialisation order. -/
theorem strictMono_base {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    [AlgebraicGeometry.IsOpenImmersion g] : StrictMono g.base :=
  fun _ _ hab ↦ HomogeneityLocal.map_lt g g.isOpenEmbedding.isInducing hab

/-- The order-theoretic height of a point is invariant under isomorphisms of schemes. -/
theorem height_iso {Y Z : Scheme.{u}} (e : Y ≅ Z) (y : Y) :
    Order.height (e.hom.base y) = Order.height y := by
  have hy : e.inv.base (e.hom.base y) = y := by simp
  refine le_antisymm ?_ (Order.height_le_height_apply_of_strictMono _ (strictMono_base e.hom) y)
  have h := Order.height_le_height_apply_of_strictMono _ (strictMono_base e.inv) (e.hom.base y)
  rwa [hy] at h

variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- On an affine open subscheme the height of a point is its residue transcendence degree. -/
theorem height_eq_resTrdeg_affineOpen [LocallyOfFiniteType f] (V : X.Opens)
    (hV : IsAffineOpen V) (y : V.toScheme) :
    Order.height y = resTrdeg (V.ι ≫ f) y := by
  have hy : hV.isoSpec.inv.base (hV.isoSpec.hom.base y) = y := by simp
  have h1 : Order.height (hV.isoSpec.inv.base (hV.isoSpec.hom.base y)) =
      Order.height (hV.isoSpec.hom.base y) := height_iso hV.isoSpec.symm _
  have h2 : resTrdeg (hV.isoSpec.inv ≫ V.ι ≫ f) (hV.isoSpec.hom.base y) =
      Order.height (hV.isoSpec.hom.base y) :=
    resTrdeg_spec (A := Γ(X, V)) _ (finiteType_specAlgebraMap _) _
  have h3 := resTrdeg_comp (V.ι ≫ f) hV.isoSpec.inv (hV.isoSpec.hom.base y)
  rw [hy] at h1 h3
  rw [h1, ← h2, h3]

/-- **The global dimension formula.**  On a scheme locally of finite type over a field the height
of a point — the dimension of the closure of that point — is the transcendence degree over `k` of
its residue field. -/
theorem height_eq_resTrdeg [LocallyOfFiniteType f] (x : X) :
    Order.height x = resTrdeg f x := by
  refine le_antisymm (Order.height_le fun s hs ↦ ?_) ?_
  · obtain ⟨W, hW, hxW, -⟩ :=
      AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (X := X) (x := s.head)
        (U := ⊤) trivial
    have hmem : ∀ i, s i ∈ W := fun i ↦
      (HomogeneityLocal.le_iff_specializes.1 (s.head_le i)).mem_open W.2 hxW
    have hmemlast : s.last ∈ W := hmem _
    let s' : LTSeries W.toScheme :=
      { length := s.length
        toFun := fun i ↦ ⟨s i, hmem i⟩
        step := fun i ↦ HomogeneityLocal.lt_of_map_lt W.ι
          W.ι.isOpenEmbedding.isInducing (s.step i) }
    have hlast : W.ι.base s'.last = s.last := rfl
    calc (s.length : ℕ∞) = (s'.length : ℕ∞) := rfl
      _ ≤ Order.height s'.last := Order.length_le_height_last
      _ = resTrdeg (W.ι ≫ f) s'.last := height_eq_resTrdeg_affineOpen f W hW s'.last
      _ = resTrdeg f (W.ι.base s'.last) := resTrdeg_comp f W.ι s'.last
      _ = resTrdeg f x := by rw [hlast, hs]
  · obtain ⟨W, hW, hxW, -⟩ :=
      AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
    obtain ⟨y0, hy0⟩ : ∃ y0 : W.toScheme, W.ι.base y0 = x := ⟨⟨x, hxW⟩, rfl⟩
    calc resTrdeg f x = resTrdeg f (W.ι.base y0) := by rw [hy0]
      _ = resTrdeg (W.ι ≫ f) y0 := (resTrdeg_comp f W.ι y0).symm
      _ = Order.height y0 := (height_eq_resTrdeg_affineOpen f W hW y0).symm
      _ ≤ Order.height (W.ι.base y0) :=
          Order.height_le_height_apply_of_strictMono _ (strictMono_base W.ι) y0
      _ = Order.height x := by rw [hy0]

end Global

/-! ## The dimension function -/

section DimensionFunctionSection

variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- The residue transcendence degree of a point of an affine open is finite. -/
theorem resTrdeg_affineOpen_ne_top [LocallyOfFiniteType f] (V : X.Opens)
    (hV : IsAffineOpen V) (y : V.toScheme) : resTrdeg (V.ι ≫ f) y ≠ ⊤ := by
  have hy : hV.isoSpec.inv.base (hV.isoSpec.hom.base y) = y := by simp
  have h3 := resTrdeg_comp (V.ι ≫ f) hV.isoSpec.inv (hV.isoSpec.hom.base y)
  rw [hy] at h3
  rw [← h3]
  exact resTrdeg_spec_ne_top (A := Γ(X, V)) _ (finiteType_specAlgebraMap _) _

/-- The residue transcendence degree of a scheme locally of finite type over a field is finite at
every point. -/
theorem resTrdeg_ne_top [LocallyOfFiniteType f] (x : X) : resTrdeg f x ≠ ⊤ := by
  obtain ⟨W, hW, hxW, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  obtain ⟨y0, hy0⟩ : ∃ y0 : W.toScheme, W.ι.base y0 = x := ⟨⟨x, hxW⟩, rfl⟩
  rw [← hy0, ← resTrdeg_comp f W.ι y0]
  exact resTrdeg_affineOpen_ne_top f W hW y0

/-- **The canonical dimension function** of a scheme locally of finite type over a field: the
dimension of the closure of a point is the transcendence degree of its residue field. -/
noncomputable def dimensionFunction [LocallyOfFiniteType f] : DimensionFunction X where
  toFun x := ((resTrdeg f x).toNat : ℤ)
  nonnegative _ := Int.natCast_nonneg _
  height_eq x := by
    rw [height_eq_resTrdeg f x]
    simp [ENat.natCast_toNat (resTrdeg_ne_top f x)]

@[simp] theorem dimensionFunction_apply [LocallyOfFiniteType f] (x : X) :
    dimensionFunction f x = ((resTrdeg f x).toNat : ℤ) := rfl

/-- The canonical dimension functions are compatible with open immersions.  This is the
compatibility hypothesis `hdim` that all restriction statements about graded cycles carry. -/
theorem dimensionFunction_comp [LocallyOfFiniteType f] {Y : Scheme.{u}} (g : Y ⟶ X)
    [AlgebraicGeometry.IsOpenImmersion g] (y : Y) :
    dimensionFunction (g ≫ f) y = dimensionFunction f (g.base y) := by
  simp only [dimensionFunction_apply, resTrdeg_comp]

/-- **Homogeneity of principal divisors** on a scheme locally of finite type over a field, for the
canonical dimension function. -/
theorem principalDivisorsHomogeneous [LocallyOfFiniteType f] :
    PrincipalDivisorsHomogeneous X (dimensionFunction f) := by
  refine HomogeneityLocal.principalDivisorsHomogeneous_of_charts (fun U : X.affineOpens ↦ U)
    (AlgebraicGeometry.iSup_affineOpens_eq_top X) (dimensionFunction f)
    (fun U ↦ dimensionFunction ((U.2.isoSpec.inv ≫ U.1.ι) ≫ f)) (fun U y ↦ ?_)
    fun U ↦ hasUniversalDimensionFormula_sections f U.1 U.2
  exact dimensionFunction_comp f (U.2.isoSpec.inv ≫ U.1.ι) y

end DimensionFunctionSection

/-! ## The total space of a vector bundle -/

section Bundle

variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- The sections over an affine open of a scheme locally of finite type over a field form a
Noetherian ring. -/
theorem isNoetherianRing_sections [LocallyOfFiniteType f] (U : X.Opens) (hU : IsAffineOpen U) :
    IsNoetherianRing Γ(X, U) :=
  @Algebra.FiniteType.isNoetherianRing k Γ(X, U) _ _ (sectionsAlgebra f U)
    (finiteType_structureMap f U hU) inferInstance

variable {ι : Type u} [Finite ι] (𝓔 : VectorBundleTotalSpace.BundleData X ι)

/-- The projection of the affine space `𝔸^ι_U` to `Spec Γ(X, U)` is locally of finite type. -/
theorem locallyOfFiniteType_chartProjection (j : 𝓔.J) :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, (𝓔.chart j).1) (MvPolynomial ι Γ(X, (𝓔.chart j).1))))) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact (RingHom.finiteType_algebraMap (A := Γ(X, (𝓔.chart j).1))
    (B := MvPolynomial ι Γ(X, (𝓔.chart j).1))).mpr inferInstance

/-- **The total space of a vector bundle is again locally of finite type over the base field.**
The trivialising charts are affine spaces over the charts of the base. -/
instance locallyOfFiniteType_proj [LocallyOfFiniteType f] :
    LocallyOfFiniteType (𝓔.proj ≫ f) := by
  let _ := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType)
    (Q := RingHom.FiniteType)
  refine IsZariskiLocalAtSource.of_iSup_eq_top (fun j : 𝓔.J ↦ (𝓔.chartι j).opensRange)
    𝓔.iSup_opensRange_chartι fun j ↦ ?_
  have h1 : 𝓔.chartι j ≫ 𝓔.proj ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, (𝓔.chart j).1)
        (MvPolynomial ι Γ(X, (𝓔.chart j).1)))) ≫ (𝓔.chart j).2.isoSpec.inv ≫
        ((𝓔.chart j).1.ι ≫ f) := by
    rw [← Category.assoc, ← (𝓔.isPullback_chart j).w]
    simp only [Category.assoc]
  have hchart : LocallyOfFiniteType (𝓔.chartι j ≫ 𝓔.proj ≫ f) := by
    rw [h1]
    have _ := locallyOfFiniteType_chartProjection 𝓔 j
    infer_instance
  rw [← Scheme.Hom.isoOpensRange_inv_comp (𝓔.chartι j), Category.assoc]
  exact IsZariskiLocalAtSource.comp hchart _

/-- **The dimension shift along a vector bundle.**  The generic point of the fibre over `x` has
dimension `dim x + rank`. -/
theorem dimensionFunction_bundlePoint [LocallyOfFiniteType f] (x : X) :
    dimensionFunction (𝓔.proj ≫ f) (BundlePullbackGlobal.bundlePoint 𝓔 x) =
      dimensionFunction f x + (Nat.card ι : ℤ) := by
  have hx := BundlePullbackGlobal.mem_chart_chartIndex 𝓔 x
  have _ := isNoetherianRing_sections f (𝓔.chart (BundlePullbackGlobal.chartIndex 𝓔 x)).1
    (𝓔.chart (BundlePullbackGlobal.chartIndex 𝓔 x)).2
  obtain ⟨y0, hy0⟩ :
      ∃ y0 : (𝓔.chart (BundlePullbackGlobal.chartIndex 𝓔 x)).1.toScheme,
        (𝓔.chart (BundlePullbackGlobal.chartIndex 𝓔 x)).1.ι.base y0 = x := ⟨⟨x, hx⟩, rfl⟩
  rw [← hy0]
  exact BundlePullbackGlobal.dimension_bundlePoint_chart 𝓔 _ (dimensionFunction f)
    (dimensionFunction (𝓔.proj ≫ f))
    (dimensionFunction (((𝓔.chart (BundlePullbackGlobal.chartIndex 𝓔 x)).2.isoSpec.inv ≫
      (𝓔.chart (BundlePullbackGlobal.chartIndex 𝓔 x)).1.ι) ≫ f))
    (dimensionFunction (𝓔.chartι (BundlePullbackGlobal.chartIndex 𝓔 x) ≫ 𝓔.proj ≫ f))
    (fun y ↦ dimensionFunction_comp f _ y)
    (fun q ↦ dimensionFunction_comp (𝓔.proj ≫ f) _ q) y0

/-- Homogeneity of principal divisors on the total space of a vector bundle over a scheme
locally of finite type over a field. -/
theorem principalDivisorsHomogeneous_totalSpace [LocallyOfFiniteType f] :
    PrincipalDivisorsHomogeneous 𝓔.totalSpace (dimensionFunction (𝓔.proj ≫ f)) :=
  HomogeneityLocal.principalDivisorsHomogeneous_totalSpace 𝓔
    (dimensionFunction (𝓔.proj ≫ f))
    (fun j ↦ dimensionFunction (𝓔.chartι j ≫ 𝓔.proj ≫ f))
    (fun j q ↦ dimensionFunction_comp (𝓔.proj ≫ f) (𝓔.chartι j) q)
    fun j ↦ hasUniversalDimensionFormula_sections f (𝓔.chart j).1 (𝓔.chart j).2

/-- **The graded flat pullback along the total space of a vector bundle**, with no chart
hypotheses: the dimension shift is supplied by `dimensionFunction_bundlePoint`. -/
noncomputable def flatPullbackBundleFiniteType [LocallyOfFiniteType f] (i : ℤ) :
    cyclesOfDimension X (dimensionFunction f) i →ₗ[ℚ]
      cyclesOfDimension 𝓔.totalSpace (dimensionFunction (𝓔.proj ≫ f))
        (i + (Nat.card ι : ℤ)) :=
  BundlePullbackGlobal.flatPullbackBundleGlobal 𝓔 (dimensionFunction f)
    (dimensionFunction (𝓔.proj ≫ f)) (dimensionFunction_bundlePoint f 𝓔) i

/-- The graded flat pullback along a vector bundle is injective. -/
theorem flatPullbackBundleFiniteType_injective [LocallyOfFiniteType f] (i : ℤ) :
    Function.Injective (flatPullbackBundleFiniteType f 𝓔 i) :=
  BundlePullbackGlobal.flatPullbackBundleGlobal_injective 𝓔 _ _ _ i

end Bundle

end GromovWitten.AlgebraicGeometry.IntersectionTheory.FiniteTypeDimension
