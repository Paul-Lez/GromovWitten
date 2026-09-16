/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.FittingIdeals
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Globalised differential Fitting ideals and the relative Fitting locus

This file upgrades the affine, presentation-dependent Fitting ideals of
`GromovWitten/AlgebraicGeometry/FittingIdeals.lean` to a presentation-free construction and then
to a genuine quasi-coherent ideal sheaf on the source of a relative scheme.

## Main constructions

* `Module.Presentation.baseChange`: the base change of a presentation of an `A`-module `M` along
  `A → B` presents any base change `N` of `M`.  This is proved through the universal property
  (`Module.Presentation.baseChangeCore`), so no right-exactness input is needed.
* `Module.fittingIdeal A M i`: the `i`-th Fitting ideal of a module, defined with no reference to
  a presentation as the supremum over all finite presentations.  `Module.fittingIdeal_eq` shows
  that it is computed by *every* finite presentation.
* `Algebra.differentialFittingIdeal R S i`: the `i`-th Fitting ideal of `Ω[S⁄R]`.
* `RelativeFittingLocus.idealSheaf f i`: for `f : X ⟶ Y` locally of finite presentation with `Y`
  affine and `X` arbitrary, a genuine `X.IdealSheafData` whose value on an affine open `V` is
  `Algebra.differentialFittingIdeal Γ(Y, ⊤) Γ(X, V) i`.
* `RelativeFittingLocus.locus f i` and `RelativeFittingLocus.locusι f i`: the corresponding closed
  subscheme of `X` and its closed immersion.

## Main results

* `Module.fittingIdeal_baseChange`: Fitting ideals commute with arbitrary base change.
* `Algebra.differentialFittingIdeal_of_formallyEtale` and
  `Algebra.differentialFittingIdeal_of_isLocalization`: differential Fitting ideals extend along
  formally étale maps of the total space, in particular along localisations.  The latter is
  exactly the gluing datum `RelativeFittingLocus.map_idealOn_basicOpen`.
* `Algebra.differentialFittingIdeal_baseChange`: compatibility with base change of the base ring.
* `Algebra.differentialFittingIdeal_of_surjective_base`: enlarging the base along a surjection
  does not change the differential Fitting ideals.
* `RelativeFittingLocus.idealSheaf_zero_eq_top_iff`: the zeroth Fitting ideal sheaf is the unit
  ideal sheaf exactly for formally unramified morphisms; equivalently the zeroth Fitting locus is
  empty (`RelativeFittingLocus.isEmpty_locus_zero_iff`).
* `RelativeFittingLocus.idealOn_comp_etale`: the construction pulls back along étale maps of the
  source, which is what makes étale charts (such as node charts) compute the Fitting locus.
* `RelativeFittingLocus.map_idealOn_top_specMap`: for a morphism of affine schemes the ideal on
  the top open is the differential Fitting ideal of the corresponding ring map, transported along
  `Γ(Spec B, ⊤) ≅ B`.

## Scope

The target `Y` is required to be affine.  For a general target the ideal on an affine open `V` of
`X` would have to be computed against `Γ(Y, U)` for an affine open `U ⊆ Y` containing the image of
`V`, and independence of the choice of `U` is not available here: two affine opens of a
non-separated `Y` need not be comparable, so the localisation argument used for
`map_idealOn_basicOpen` does not apply.  Everything else — in particular the source `X` — is
completely general.
-/

namespace GromovWitten.AlgebraicGeometry

open CategoryTheory
open _root_.AlgebraicGeometry

universe u v w

noncomputable section

namespace Module.Presentation

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
variable {B : Type*} [CommRing B] [Algebra A B]
variable {N : Type*} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]

/-- Push the coefficients of a system of relations along `algebraMap A B`. -/
def baseChangeRelations (rel : _root_.Module.Relations A)
    (B : Type*) [CommRing B] [Algebra A B] : _root_.Module.Relations B where
  G := rel.G
  R := rel.R
  relation r := Finsupp.mapRange (algebraMap A B) (map_zero _) (rel.relation r)

@[simp]
theorem baseChangeRelations_relation (rel : _root_.Module.Relations A) (r : rel.R) :
    (baseChangeRelations rel B).relation r =
      Finsupp.mapRange (algebraMap A B) (map_zero _) (rel.relation r) := rfl

/-- Evaluating a linear combination with coefficients pushed to `B` agrees with evaluating it
over `A`. -/
theorem linearCombination_mapRange {G : Type*} (var : G → N) (x : G →₀ A) :
    Finsupp.linearCombination B var (Finsupp.mapRange (algebraMap A B) (map_zero _) x) =
      Finsupp.linearCombination A var x := by
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
    Finsupp.sum_mapRange_index (fun i ↦ zero_smul B (var i))]
  exact Finsupp.sum_congr fun i _ ↦ algebraMap_smul B _ _

/-- The base-changed solution: the images of the generators under a linear map to a module over
the bigger ring. -/
def baseChangeSolution (P : _root_.Module.Presentation A M) (g : M →ₗ[A] N) :
    (baseChangeRelations P.toRelations B).Solution N where
  var x := g (P.var x)
  linearCombination_var_relation r := by
    refine (linearCombination_mapRange (B := B) (fun x ↦ g (P.var x)) (P.relation r)).trans ?_
    have h : ∀ l : P.G →₀ A, Finsupp.linearCombination A (fun x ↦ g (P.var x)) l =
        g (Finsupp.linearCombination A P.var l) := by
      intro l
      simp [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    rw [h, P.linearCombination_var_relation r, map_zero]

theorem baseChangeSolution_var (P : _root_.Module.Presentation A M) (g : M →ₗ[A] N) (x : P.G) :
    (baseChangeSolution (B := B) P g).var x = g (P.var x) := rfl

variable (P : _root_.Module.Presentation A M)

/-- A solution over `B` of the base-changed relations is a solution over `A` of the original
relations, after restricting scalars along `algebraMap A B`. -/
private def restrictedSolution {N' : Type*} [AddCommGroup N'] [Module B N']
    (s : (baseChangeRelations P.toRelations B).Solution N') :
    letI : Module A N' := Module.compHom N' (algebraMap A B)
    P.toRelations.Solution N' :=
  letI : Module A N' := Module.compHom N' (algebraMap A B)
  haveI : IsScalarTower A B N' := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  { var := s.var
    linearCombination_var_relation := fun r ↦
      (linearCombination_mapRange (B := B) s.var (P.relation r)).symm.trans
        (s.linearCombination_var_relation r) }

/-- The linear map out of the base change induced by a solution of the base-changed relations. -/
private def baseChangeDesc (g : M →ₗ[A] N) (hg : IsBaseChange B g)
    {N' : Type*} [AddCommGroup N'] [Module B N']
    (s : (baseChangeRelations P.toRelations B).Solution N') : N →ₗ[B] N' :=
  letI : Module A N' := Module.compHom N' (algebraMap A B)
  haveI : IsScalarTower A B N' := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  hg.lift (P.toIsPresentation.desc (restrictedSolution P s))

private theorem baseChangeDesc_var (g : M →ₗ[A] N) (hg : IsBaseChange B g)
    {N' : Type*} [AddCommGroup N'] [Module B N']
    (s : (baseChangeRelations P.toRelations B).Solution N') (x : P.G) :
    baseChangeDesc P g hg s (g (P.var x)) = s.var x := by
  let _inst : Module A N' := Module.compHom N' (algebraMap A B)
  have : IsScalarTower A B N' := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact (hg.lift_eq (P.toIsPresentation.desc (restrictedSolution P s)) (P.var x)).trans
    (P.toIsPresentation.desc_var (restrictedSolution P s) x)

private theorem baseChangeDesc_injective (g : M →ₗ[A] N) (hg : IsBaseChange B g)
    {N' : Type*} [AddCommGroup N'] [Module B N'] {f f' : N →ₗ[B] N'}
    (h : (baseChangeSolution P g).postcomp f = (baseChangeSolution P g).postcomp f') :
    f = f' := by
  let _inst : Module A N' := Module.compHom N' (algebraMap A B)
  have : IsScalarTower A B N' := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  refine hg.algHom_ext f f' fun m ↦ ?_
  have key : (f.restrictScalars A).comp g = (f'.restrictScalars A).comp g := by
    refine P.toIsPresentation.postcomp_injective ?_
    ext x
    exact _root_.Module.Relations.Solution.congr_var h x
  exact congrFun (congrArg (fun φ : M →ₗ[A] N' ↦ (φ : M → N')) key) m

/-- The base change of a finite presentation is a presentation of the base-changed module. -/
def baseChangeCore (g : M →ₗ[A] N) (hg : IsBaseChange B g) :
    _root_.Module.Relations.Solution.IsPresentationCore.{w}
      (baseChangeSolution (B := B) P g) where
  desc s := baseChangeDesc P g hg s
  postcomp_desc s := by
    ext x
    exact baseChangeDesc_var P g hg s x
  postcomp_injective h := baseChangeDesc_injective P g hg h

/-- The base-changed solution is a presentation of the base-changed module. -/
theorem baseChangeSolution_isPresentation (g : M →ₗ[A] N) (hg : IsBaseChange B g) :
    (baseChangeSolution (B := B) P g).IsPresentation :=
  (baseChangeCore P g hg).isPresentation

/-- The base change along `A → B` of a presentation of an `A`-module `M` is a presentation of
any base change `N` of `M`. -/
def baseChange (P : _root_.Module.Presentation A M) (g : M →ₗ[A] N) (hg : IsBaseChange B g) :
    _root_.Module.Presentation B N :=
  _root_.Module.Presentation.ofIsPresentation (baseChangeSolution_isPresentation P g hg)

instance baseChangeFintypeG (g : M →ₗ[A] N) (hg : IsBaseChange B g) [Fintype P.G] :
    Fintype (baseChange P g hg).G := ‹Fintype P.G›

instance baseChangeFintypeR (g : M →ₗ[A] N) (hg : IsBaseChange B g) [Fintype P.R] :
    Fintype (baseChange P g hg).R := ‹Fintype P.R›

theorem baseChange_relationMatrix (g : M →ₗ[A] N) (hg : IsBaseChange B g) :
    relationMatrix (baseChange P g hg) =
      fun (x : P.G) (r : P.R) ↦ algebraMap A B (relationMatrix P x r) := rfl

omit [Algebra A B] in
/-- Fitting ideals of a finite presentation increase with the index. -/
theorem fittingIdeal_le_succ [Fintype P.G] [Fintype P.R] (i : ℕ) :
    fittingIdeal P i ≤ fittingIdeal P (i + 1) := by
  unfold fittingIdeal
  rcases le_or_gt (Fintype.card P.G) i with h | h
  · rw [Nat.sub_eq_zero_of_le h, Nat.sub_eq_zero_of_le (h.trans (Nat.le_succ i))]
  · have hsub : Fintype.card P.G - i = (Fintype.card P.G - (i + 1)) + 1 := by omega
    rw [hsub]
    exact Matrix.minorIdeal_succ_le _ _

/-- Determinantal Fitting ideals of a finite presentation are compatible with base change. -/
theorem fittingIdeal_baseChange (g : M →ₗ[A] N) (hg : IsBaseChange B g)
    [Fintype P.G] [Fintype P.R] (i : ℕ) :
    fittingIdeal (baseChange P g hg) i = (fittingIdeal P i).map (algebraMap A B) := by
  rw [map_fittingIdeal_relationMatrix P (algebraMap A B) i]
  rfl

end Module.Presentation

/-- The `i`-th Fitting ideal of a module, defined without reference to a presentation.  It is
the supremum of the determinantal Fitting ideals of all finite presentations; by
`Module.fittingIdeal_eq` it coincides with each of them as soon as one exists. -/
def Module.fittingIdeal (A : Type*) [CommRing A] (M : Type*) [AddCommGroup M] [Module A M]
    (i : ℕ) : Ideal A :=
  ⨆ (P : _root_.Module.Presentation.{0, 0} A M) (hG : Fintype P.G) (hR : Fintype P.R),
    @Module.Presentation.fittingIdeal A _ M _ _ P hG hR i

namespace Module

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

/-- Every finite presentation computes the presentation-free Fitting ideal. -/
theorem fittingIdeal_eq (P : _root_.Module.Presentation.{w, v} A M)
    [Fintype P.G] [Fintype P.R] (i : ℕ) :
    Module.fittingIdeal A M i = Module.Presentation.fittingIdeal P i := by
  refine le_antisymm (iSup_le fun Q ↦ iSup_le fun hG ↦ iSup_le fun hR ↦ ?_) ?_
  · exact le_of_eq (Module.Presentation.fittingIdeal_eq Q P i)
  · have hfp : _root_.Module.FinitePresentation A M := P.finitePresentation
    obtain ⟨Q, hQG, hQR⟩ :
        ∃ Q : _root_.Module.Presentation.{0, 0} A M, Finite Q.G ∧ Finite Q.R :=
      _root_.Module.finitePresentation_iff_exists_presentation.mp hfp
    have hQG' : Fintype Q.G := Fintype.ofFinite Q.G
    have hQR' : Fintype Q.R := Fintype.ofFinite Q.R
    calc Module.Presentation.fittingIdeal P i
        = Module.Presentation.fittingIdeal Q i := Module.Presentation.fittingIdeal_eq P Q i
      _ ≤ Module.fittingIdeal A M i :=
          le_iSup_of_le Q (le_iSup_of_le hQG' (le_iSup_of_le hQR' le_rfl))

/-- Fitting ideals only depend on the isomorphism class of the module. -/
theorem fittingIdeal_of_linearEquiv {M' : Type*} [AddCommGroup M'] [Module A M']
    [_root_.Module.FinitePresentation A M] (e : M ≃ₗ[A] M') (i : ℕ) :
    Module.fittingIdeal A M i = Module.fittingIdeal A M' i := by
  obtain ⟨P, hPG, hPR⟩ :
      ∃ P : _root_.Module.Presentation.{0, 0} A M, Finite P.G ∧ Finite P.R :=
    _root_.Module.finitePresentation_iff_exists_presentation.mp ‹_›
  let hPG' : Fintype P.G := Fintype.ofFinite P.G
  let hPR' : Fintype P.R := Fintype.ofFinite P.R
  let hQG : Fintype (P.ofLinearEquiv e).G := hPG'
  let hQR : Fintype (P.ofLinearEquiv e).R := hPR'
  rw [Module.fittingIdeal_eq P i, Module.fittingIdeal_eq (P.ofLinearEquiv e) i]
  rfl

/-- The Fitting ideals of a finitely presented module increase with the index. -/
theorem fittingIdeal_le_succ [_root_.Module.FinitePresentation A M] (i : ℕ) :
    Module.fittingIdeal A M i ≤ Module.fittingIdeal A M (i + 1) := by
  obtain ⟨P, hPG, hPR⟩ :
      ∃ P : _root_.Module.Presentation.{0, 0} A M, Finite P.G ∧ Finite P.R :=
    _root_.Module.finitePresentation_iff_exists_presentation.mp ‹_›
  have hPG' : Fintype P.G := Fintype.ofFinite P.G
  have hPR' : Fintype P.R := Fintype.ofFinite P.R
  rw [Module.fittingIdeal_eq P i, Module.fittingIdeal_eq P (i + 1)]
  exact Module.Presentation.fittingIdeal_le_succ P i

variable {B : Type*} [CommRing B] [Algebra A B]
variable {N : Type*} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]

/-- Fitting ideals of finitely presented modules are compatible with arbitrary base change. -/
theorem fittingIdeal_baseChange [_root_.Module.FinitePresentation A M]
    (g : M →ₗ[A] N) (hg : IsBaseChange B g) (i : ℕ) :
    Module.fittingIdeal B N i = (Module.fittingIdeal A M i).map (algebraMap A B) := by
  obtain ⟨P, hPG, hPR⟩ :
      ∃ P : _root_.Module.Presentation.{0, 0} A M, Finite P.G ∧ Finite P.R :=
    _root_.Module.finitePresentation_iff_exists_presentation.mp ‹_›
  have hPG' : Fintype P.G := Fintype.ofFinite P.G
  have hPR' : Fintype P.R := Fintype.ofFinite P.R
  rw [Module.fittingIdeal_eq (Module.Presentation.baseChange P g hg) i,
    Module.fittingIdeal_eq P i, Module.Presentation.fittingIdeal_baseChange P g hg i]

end Module

/-! ### Differential Fitting ideals of a relative algebra -/

namespace Algebra

variable (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]

/-- Kähler differentials of a finitely presented algebra are a finitely presented module. -/
instance finitePresentation_kaehlerDifferential [_root_.Algebra.FinitePresentation R S] :
    _root_.Module.FinitePresentation S Ω[S⁄R] :=
  (_root_.Algebra.Presentation.ofFinitePresentation R S).differentials.finitePresentation

/-- The `i`-th differential Fitting ideal of a relative algebra: the `i`-th Fitting ideal of its
module of Kähler differentials.  No presentation is involved in the definition. -/
def differentialFittingIdeal (i : ℕ) : Ideal S :=
  Module.fittingIdeal S Ω[S⁄R] i

variable {R S}

/-- Every finite algebra presentation computes the differential Fitting ideal. -/
theorem differentialFittingIdeal_eq_of_presentation {ι σ : Type*} [Fintype ι] [Fintype σ]
    (P : _root_.Algebra.Presentation R S ι σ) (i : ℕ) :
    differentialFittingIdeal R S i = AlgebraPresentation.differentialFittingIdeal P i :=
  Module.fittingIdeal_eq P.differentials i

variable (R S)

/-- The differential Fitting ideal computed from the algebra structure induced by `algebraMap`
agrees with the one computed from the given algebra structure. -/
theorem differentialFittingIdeal_toAlgebra (i : ℕ) :
    @differentialFittingIdeal R _ S _ (algebraMap R S).toAlgebra i =
      differentialFittingIdeal R S i :=
  congrArg (fun inst : _root_.Algebra R S ↦ @differentialFittingIdeal R _ S _ inst i)
    (_root_.Algebra.algebra_ext _ _ fun _ ↦ rfl)

/-- The zeroth differential Fitting ideal is the unit ideal exactly for formally unramified
algebras. -/
theorem differentialFittingIdeal_zero_eq_top_iff [_root_.Algebra.FinitePresentation R S] :
    differentialFittingIdeal R S 0 = ⊤ ↔ _root_.Algebra.FormallyUnramified R S := by
  rw [differentialFittingIdeal_eq_of_presentation
      (_root_.Algebra.Presentation.ofFinitePresentation R S) 0]
  exact AlgebraPresentation.differentialFittingIdeal_zero_eq_top_iff_formallyUnramified _

/-- The support of the module of Kähler differentials is the zero locus of the zeroth
differential Fitting ideal. -/
theorem support_kaehlerDifferential_eq_zeroLocus [_root_.Algebra.FinitePresentation R S] :
    _root_.Module.support S Ω[S⁄R] =
      PrimeSpectrum.zeroLocus (differentialFittingIdeal R S 0) := by
  rw [differentialFittingIdeal_eq_of_presentation
      (_root_.Algebra.Presentation.ofFinitePresentation R S) 0]
  exact AlgebraPresentation.support_kaehlerDifferential_eq_zeroLocus_differentialFittingIdeal_zero _

/-- The affine formally unramified locus is the complement of the zero locus of the zeroth
differential Fitting ideal. -/
theorem unramifiedLocus_eq_compl_zeroLocus [_root_.Algebra.FinitePresentation R S] :
    _root_.Algebra.unramifiedLocus R S =
      (PrimeSpectrum.zeroLocus (differentialFittingIdeal R S 0))ᶜ := by
  rw [_root_.Algebra.unramifiedLocus_eq_compl_support, support_kaehlerDifferential_eq_zeroLocus]

section FormallyEtale

variable (T : Type*) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- Differential Fitting ideals are compatible with formally étale extensions of the total space:
the Fitting ideal upstairs is the extension of the Fitting ideal downstairs.  In particular this
applies to localizations and to étale charts. -/
theorem differentialFittingIdeal_of_formallyEtale [_root_.Algebra.FinitePresentation R S]
    [_root_.Algebra.FormallyEtale S T] (i : ℕ) :
    differentialFittingIdeal R T i =
      (differentialFittingIdeal R S i).map (algebraMap S T) :=
  Module.fittingIdeal_baseChange (KaehlerDifferential.map R R S T)
    (KaehlerDifferential.isBaseChange_of_formallyEtale R S T) i

/-- Differential Fitting ideals localize: the Fitting ideal of a localization of `S` is the
extension of the Fitting ideal of `S`. -/
theorem differentialFittingIdeal_of_isLocalization [_root_.Algebra.FinitePresentation R S]
    (p : Submonoid S) [IsLocalization p T] (i : ℕ) :
    differentialFittingIdeal R T i =
      (differentialFittingIdeal R S i).map (algebraMap S T) :=
  have := _root_.Algebra.FormallyEtale.of_isLocalization (Rₘ := T) p
  differentialFittingIdeal_of_formallyEtale R S T i

end FormallyEtale

section SurjectiveBase

variable (T : Type*) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- If the base ring surjects onto an intermediate ring, the relative Kähler differentials over
the two bases agree. -/
def kaehlerEquivOfSurjectiveBase (h : Function.Surjective (algebraMap R S)) :
    Ω[T⁄R] ≃ₗ[T] Ω[T⁄S] := by
  refine LinearEquiv.ofBijective (KaehlerDifferential.map R S T T)
    ⟨?_, KaehlerDifferential.map_surjective R S T⟩
  have hunr : _root_.Algebra.FormallyUnramified R S :=
    (RingHom.formallyUnramified_algebraMap (R := R) (S := S)).mp
      (RingHom.FormallyUnramified.of_surjective h)
  have hsub : Subsingleton Ω[S⁄R] := (_root_.Algebra.formallyUnramified_iff R S).mp hunr
  have hzero : ∀ z : TensorProduct S T Ω[S⁄R], z = 0 := by
    intro z
    induction z with
    | zero => rfl
    | tmul t ω => rw [Subsingleton.elim ω 0, TensorProduct.tmul_zero]
    | add a b ha hb => rw [ha, hb, add_zero]
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (KaehlerDifferential.exact_mapBaseChange_map R S T x).mp hx
  rw [hzero y, map_zero]

/-- Enlarging the base ring along a surjection does not change the differential Fitting
ideals. -/
theorem differentialFittingIdeal_of_surjective_base
    (h : Function.Surjective (algebraMap R S)) [_root_.Algebra.FinitePresentation S T] (i : ℕ) :
    differentialFittingIdeal S T i = differentialFittingIdeal R T i :=
  Module.fittingIdeal_of_linearEquiv (kaehlerEquivOfSurjectiveBase R S T h).symm i

end SurjectiveBase

section BaseChange

variable (A B : Type*) [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
variable [IsScalarTower R A B] [IsScalarTower R S B]

/-- For a pushout square of rings, `Ω[B⁄S]` is the base change of `Ω[A⁄R]` along `A → B`. -/
theorem isBaseChange_kaehlerDifferential [_root_.Algebra.IsPushout R S A B] :
    IsBaseChange B (KaehlerDifferential.map R S A B) := by
  refine IsBaseChange.of_equiv (KaehlerDifferential.tensorKaehlerEquiv R S A B) fun x ↦ ?_
  have hx : x ∈ (⊤ : Submodule A Ω[A⁄R]) := trivial
  rw [← KaehlerDifferential.span_range_derivation] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    simp [KaehlerDifferential.map_D]
  | zero => simp
  | add x y _ _ hx hy => simp [TensorProduct.tmul_add, hx, hy]
  | smul a x _ hx =>
    have h1 : (1 : B) ⊗ₜ[A] (a • x) = algebraMap A B a • ((1 : B) ⊗ₜ[A] x) := by
      rw [algebraMap_smul, TensorProduct.tmul_smul]
    rw [h1, map_smul, hx, LinearMap.map_smul, algebraMap_smul]

/-- Differential Fitting ideals are compatible with base change: for a pushout square of rings,
the Fitting ideal of `Ω[B⁄S]` is the extension of the Fitting ideal of `Ω[A⁄R]`. -/
theorem differentialFittingIdeal_baseChange [_root_.Algebra.IsPushout R S A B]
    [_root_.Algebra.FinitePresentation R A] (i : ℕ) :
    differentialFittingIdeal S B i =
      (differentialFittingIdeal R A i).map (algebraMap A B) :=
  Module.fittingIdeal_baseChange (KaehlerDifferential.map R S A B)
    (isBaseChange_kaehlerDifferential R S A B) i

end BaseChange

end Algebra

/-! ### The relative differential Fitting ideal sheaf -/

namespace RelativeFittingLocus

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y]

omit [IsAffine Y] in
/-- Every affine open of the source lies over the whole affine target. -/
theorem le_preimage_top (V : X.Opens) : V ≤ f ⁻¹ᵁ (⊤ : Y.Opens) := by simp

/-- Sections over an affine open of the source form an algebra over the global sections of an
affine target. -/
@[instance_reducible]
def baseAlgebra (V : X.affineOpens) : Algebra Γ(Y, ⊤) Γ(X, V.1) :=
  (f.appLE ⊤ V.1 (le_preimage_top f V.1)).hom.toAlgebra

theorem finitePresentation_baseAlgebra [LocallyOfFinitePresentation f] (V : X.affineOpens) :
    @_root_.Algebra.FinitePresentation Γ(Y, ⊤) Γ(X, V.1) _ _ (baseAlgebra f V) :=
  f.finitePresentation_appLE (isAffineOpen_top Y) V.2 _

/-- The ideal cut out on an affine open of the source by the `i`-th differential Fitting ideal of
the relative Kähler differentials. -/
def idealOn (i : ℕ) (V : X.affineOpens) : Ideal Γ(X, V.1) :=
  @Algebra.differentialFittingIdeal Γ(Y, ⊤) _ Γ(X, V.1) _ (baseAlgebra f V) i

/-- The Fitting ideals of the affine pieces are compatible with restriction to basic opens: this
is the localisation statement that makes them glue to an ideal sheaf. -/
theorem map_idealOn_basicOpen [LocallyOfFinitePresentation f] (i : ℕ) (V : X.affineOpens)
    (g : Γ(X, V.1)) :
    (idealOn f i V).map (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom =
      idealOn f i (X.affineBasicOpen g) := by
  let iV : Algebra Γ(Y, ⊤) Γ(X, V.1) := baseAlgebra f V
  let iW : Algebra Γ(Y, ⊤) Γ(X, X.basicOpen g) := baseAlgebra f (X.affineBasicOpen g)
  have htower : IsScalarTower Γ(Y, ⊤) Γ(X, V.1) Γ(X, X.basicOpen g) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    exact congrArg CommRingCat.Hom.hom
      (Scheme.Hom.appLE_map f (le_preimage_top f V.1)
        (homOfLE (X.basicOpen_le g) : X.basicOpen g ⟶ V.1).op).symm
  have hloc : IsLocalization.Away g Γ(X, X.basicOpen g) := V.2.isLocalization_basicOpen g
  have hfp : _root_.Algebra.FinitePresentation Γ(Y, ⊤) Γ(X, V.1) :=
    finitePresentation_baseAlgebra f V
  exact (Algebra.differentialFittingIdeal_of_isLocalization Γ(Y, ⊤) Γ(X, V.1)
    Γ(X, X.basicOpen g) (Submonoid.powers g) i).symm

/-- The relative differential Fitting ideal sheaf of a morphism locally of finite presentation
over an affine base.  Its value on an affine open `V` of the source is the `i`-th Fitting ideal of
the relative Kähler differentials of `Γ(X, V)` over `Γ(Y, ⊤)`. -/
def idealSheaf [LocallyOfFinitePresentation f] (i : ℕ) : X.IdealSheafData where
  ideal := idealOn f i
  map_ideal_basicOpen := map_idealOn_basicOpen f i

@[simp]
theorem idealSheaf_ideal [LocallyOfFinitePresentation f] (i : ℕ) (V : X.affineOpens) :
    (idealSheaf f i).ideal V = idealOn f i V :=
  rfl

variable [LocallyOfFinitePresentation f]

/-- The `i`-th relative differential Fitting locus: the closed subscheme of the source cut out by
the `i`-th differential Fitting ideal sheaf.  For a relative curve, `i = 1` gives the relative
critical (singular) locus. -/
abbrev locus (i : ℕ) : Scheme.{u} :=
  (idealSheaf f i).subscheme

/-- The canonical immersion of the relative Fitting locus into the source. -/
abbrev locusι (i : ℕ) : locus f i ⟶ X :=
  (idealSheaf f i).subschemeι

@[simp]
theorem range_locusι (i : ℕ) :
    Set.range (locusι f i) = ((idealSheaf f i).support : Set X) :=
  Scheme.IdealSheafData.range_subschemeι _

instance locusι_isClosedImmersion (i : ℕ) : IsClosedImmersion (locusι f i) :=
  IsClosedImmersion.of_isPreimmersion _ (by
    rw [locusι, Scheme.IdealSheafData.range_subschemeι]
    exact (idealSheaf f i).support.2)

/-- The kernel of the immersion of the Fitting locus is exactly the Fitting ideal sheaf. -/
@[simp]
theorem ker_locusι (i : ℕ) : (locusι f i).ker = idealSheaf f i :=
  Scheme.IdealSheafData.ker_subschemeι _

/-- On an affine open, the zeroth Fitting ideal is the unit ideal exactly when the corresponding
ring map is formally unramified. -/
theorem idealOn_zero_eq_top_iff (V : X.affineOpens) :
    idealOn f 0 V = ⊤ ↔ (f.appLE ⊤ V.1 (le_preimage_top f V.1)).hom.FormallyUnramified := by
  let iV : Algebra Γ(Y, ⊤) Γ(X, V.1) := baseAlgebra f V
  have hfp : _root_.Algebra.FinitePresentation Γ(Y, ⊤) Γ(X, V.1) :=
    finitePresentation_baseAlgebra f V
  exact Algebra.differentialFittingIdeal_zero_eq_top_iff Γ(Y, ⊤) Γ(X, V.1)

/-- A formally unramified morphism has unit zeroth Fitting ideal sheaf. -/
theorem idealSheaf_zero_eq_top_of_formallyUnramified [FormallyUnramified f] :
    idealSheaf f 0 = ⊤ := by
  refine Scheme.IdealSheafData.ext (funext fun V ↦ ?_)
  exact (idealOn_zero_eq_top_iff f V).mpr
    (f.formallyUnramified_appLE (isAffineOpen_top Y) V.2 _)

/-- Conversely, a unit zeroth Fitting ideal sheaf forces the morphism to be formally
unramified. -/
theorem formallyUnramified_of_idealSheaf_zero_eq_top (h : idealSheaf f 0 = ⊤) :
    FormallyUnramified f := by
  refine ⟨fun {U} hU {V} hV e ↦ ?_⟩
  have htop : idealOn f 0 ⟨V, hV⟩ = ⊤ := by
    rw [← idealSheaf_ideal f 0 ⟨V, hV⟩, h]
    rfl
  have hcomp := (idealOn_zero_eq_top_iff f ⟨V, hV⟩).mp htop
  have hmap : (f.appLE ⊤ V (le_preimage_top f V)).hom =
      (f.appLE U V e).hom.comp (Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom := by
    rw [← CommRingCat.hom_comp]
    exact congrArg CommRingCat.Hom.hom (Scheme.Hom.map_appLE f e _).symm
  rw [hmap] at hcomp
  exact RingHom.FormallyUnramified.of_comp hcomp

/-- The zeroth relative differential Fitting ideal sheaf is the unit ideal sheaf exactly for
formally unramified morphisms. -/
theorem idealSheaf_zero_eq_top_iff :
    idealSheaf f 0 = ⊤ ↔ FormallyUnramified f :=
  ⟨formallyUnramified_of_idealSheaf_zero_eq_top f, fun _ ↦
    idealSheaf_zero_eq_top_of_formallyUnramified f⟩

/-- The support of the zeroth relative Fitting ideal sheaf is empty exactly for formally
unramified morphisms: it is the relative ramification locus. -/
theorem support_idealSheaf_zero_eq_bot_iff :
    (idealSheaf f 0).support = ⊥ ↔ FormallyUnramified f := by
  rw [Scheme.IdealSheafData.support_eq_bot_iff, idealSheaf_zero_eq_top_iff]

/-- Differential Fitting ideals are compatible with étale morphisms of the source: on affine
opens, the Fitting ideal upstairs is the extension of the Fitting ideal downstairs.  This is the
statement that makes étale charts (such as the node charts of a nodal family) compute the
relative Fitting locus. -/
theorem idealOn_comp_etale {W : Scheme.{u}} (e : W ⟶ X) [Etale e] (i : ℕ)
    (V : X.affineOpens) (W' : W.affineOpens) (h : W'.1 ≤ e ⁻¹ᵁ V.1) :
    idealOn (e ≫ f) i W' = (idealOn f i V).map (e.appLE V.1 W'.1 h).hom := by
  let iV : Algebra Γ(Y, ⊤) Γ(X, V.1) := baseAlgebra f V
  let iW : Algebra Γ(Y, ⊤) Γ(W, W'.1) := baseAlgebra (e ≫ f) W'
  let iVW : Algebra Γ(X, V.1) Γ(W, W'.1) := (e.appLE V.1 W'.1 h).hom.toAlgebra
  have htower : IsScalarTower Γ(Y, ⊤) Γ(X, V.1) Γ(W, W'.1) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    exact congrArg CommRingCat.Hom.hom
      (Scheme.Hom.appLE_comp_appLE e f ⊤ V.1 W'.1 (le_preimage_top f V.1) h).symm
  have hfp : _root_.Algebra.FinitePresentation Γ(Y, ⊤) Γ(X, V.1) :=
    finitePresentation_baseAlgebra f V
  have hetale : _root_.Algebra.Etale Γ(X, V.1) Γ(W, W'.1) := e.etale_appLE V.2 W'.2 h
  exact Algebra.differentialFittingIdeal_of_formallyEtale Γ(Y, ⊤) Γ(X, V.1) Γ(W, W'.1) i

/-- The relative differential Fitting ideal sheaves increase with the index, so the Fitting loci
form a decreasing chain of closed subschemes. -/
theorem idealSheaf_le_succ (i : ℕ) : idealSheaf f i ≤ idealSheaf f (i + 1) := by
  intro V
  let iV : Algebra Γ(Y, ⊤) Γ(X, V.1) := baseAlgebra f V
  have hfp : _root_.Algebra.FinitePresentation Γ(Y, ⊤) Γ(X, V.1) :=
    finitePresentation_baseAlgebra f V
  exact Module.fittingIdeal_le_succ (A := Γ(X, V.1)) (M := Ω[Γ(X, V.1)⁄Γ(Y, ⊤)]) i

/-- The zeroth Fitting locus is empty exactly for formally unramified morphisms. -/
theorem isEmpty_locus_zero_iff : IsEmpty (locus f 0) ↔ FormallyUnramified f := by
  rw [← idealSheaf_zero_eq_top_iff, ← Scheme.Hom.ker_eq_top_iff_isEmpty (locusι f 0),
    ker_locusι]

section Affine

variable {A B : CommRingCat.{u}} (φ : A ⟶ B)

omit [IsAffine Y] [LocallyOfFinitePresentation f] in
theorem appLE_top_top {X' Y' : Scheme.{u}} (g : X' ⟶ Y') :
    g.appLE ⊤ ⊤ (le_preimage_top g ⊤) = g.appTop := by
  have hid : X'.presheaf.map (homOfLE (le_preimage_top g ⊤)).op = 𝟙 _ := by
    rw [show (homOfLE (le_preimage_top g ⊤) : (⊤ : X'.Opens) ⟶ g ⁻¹ᵁ ⊤).op = 𝟙 _ from rfl]
    exact X'.presheaf.map_id _
  rw [Scheme.Hom.appLE, hid]
  exact Category.comp_id _

/-- For a morphism of affine schemes, the relative differential Fitting ideal on the top open is
the differential Fitting ideal of the corresponding ring map, transported along the canonical
isomorphism `Γ(Spec B, ⊤) ≅ B`. -/
theorem map_idealOn_top_specMap [LocallyOfFinitePresentation (Spec.map φ)]
    (hφ : @_root_.Algebra.FinitePresentation A B _ _ φ.hom.toAlgebra) (i : ℕ) :
    Ideal.map (Scheme.ΓSpecIso B).hom.hom
        (idealOn (Spec.map φ) i ⟨⊤, isAffineOpen_top _⟩) =
      @Algebra.differentialFittingIdeal A _ B _ φ.hom.toAlgebra i := by
  let iRS : Algebra Γ(Spec A, ⊤) Γ(Spec B, ⊤) :=
    baseAlgebra (Spec.map φ) ⟨⊤, isAffineOpen_top _⟩
  let iSB : Algebra Γ(Spec B, ⊤) B := (Scheme.ΓSpecIso B).hom.hom.toAlgebra
  let iRA : Algebra Γ(Spec A, ⊤) A := (Scheme.ΓSpecIso A).hom.hom.toAlgebra
  let iAB : Algebra A B := φ.hom.toAlgebra
  let iRB : Algebra Γ(Spec A, ⊤) B := ((Scheme.ΓSpecIso A).hom ≫ φ).hom.toAlgebra
  have tRAB : IsScalarTower Γ(Spec A, ⊤) A B :=
    IsScalarTower.of_algebraMap_eq' (CommRingCat.hom_comp _ _)
  have tRSB : IsScalarTower Γ(Spec A, ⊤) Γ(Spec B, ⊤) B := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    have h := Scheme.ΓSpecIso_naturality φ
    rw [← appLE_top_top (Spec.map φ)] at h
    exact congrArg CommRingCat.Hom.hom h.symm
  have hfpRS : _root_.Algebra.FinitePresentation Γ(Spec A, ⊤) Γ(Spec B, ⊤) :=
    finitePresentation_baseAlgebra (Spec.map φ) ⟨⊤, isAffineOpen_top _⟩
  have hetale : _root_.Algebra.Etale Γ(Spec B, ⊤) B :=
    RingHom.Etale.of_bijective (f := (Scheme.ΓSpecIso B).hom.hom)
      (Scheme.ΓSpecIso B).commRingCatIsoToRingEquiv.bijective
  have hsurj : Function.Surjective (algebraMap Γ(Spec A, ⊤) A) :=
    (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv.surjective
  have hA := Algebra.differentialFittingIdeal_of_formallyEtale Γ(Spec A, ⊤) Γ(Spec B, ⊤) B i
  have hB := @Algebra.differentialFittingIdeal_of_surjective_base Γ(Spec A, ⊤) _ A _ iRA B _
    iRB iAB tRAB hsurj hφ i
  exact (hB.trans hA).symm

end Affine

end RelativeFittingLocus

end

end GromovWitten.AlgebraicGeometry
