/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.Data.Fintype.Option

/-!
# Residue fields of `K ⊗[F] L` for a finite separable extension `L / F`

Let `F` be a field, `K` a field extension of `F` (of any degree) and `L` a finite separable
extension of `F`. We study the ring `A = K ⊗[F] L`, regarded as an `L`-algebra, through its
residue fields `κ(p) = p.asIdeal.ResidueField` at the primes `p : PrimeSpectrum A`, with the
`L`-algebra structure on `κ(p)` coming from `A`.

Instead of working with the concrete tensor product, every statement is made for an abstract
commutative ring `A` with `F`-, `K`- and `L`-algebra structures and scalar towers, together with
the hypothesis `[Algebra.IsPushout F K L A]`, which says that `A` is the pushout `K ⊗[F] L`
(the canonical map `K ⊗[F] L → A` is an isomorphism of `K`-algebras). This covers the concrete
tensor product (`TensorProduct.isPushout`, with
`Algebra.TensorProduct.rightAlgebra`) and any categorical pushout in `CommRingCat` with the
algebra structures given by the legs (`CommRingCat.isPushout_iff_isPushout`).

This is the algebra behind the étale base change of proper pushforward of cycles: for a
point `u` over `v` and an étale point `v'` over `v`, the points of the fibre product over
`(u, v')` correspond to the primes of `κ(u) ⊗[κ(v)] κ(v')`.

## Main results

* `GromovWitten.Algebra.det_pi_dependent`: the determinant of a product of endomorphisms of a
  finite family of finite free modules (possibly different modules) is the product of the
  determinants.
* `GromovWitten.Algebra.norm_pi_dependent`: the norm in a finite product of finite algebras over
  a field is the product of the norms of the components.
* `GromovWitten.Algebra.isReduced_tensor`: `A` is reduced (whatever `K`).
* `GromovWitten.Algebra.isArtinianRing_tensor`, `GromovWitten.Algebra.finite_primeSpectrum_tensor`,
  `GromovWitten.Algebra.isMaximal_of_isPrime_tensor`: `A` is Artinian (it is finite over `K`),
  so it has finitely many primes, all of them maximal.
* `GromovWitten.Algebra.finrank_tensor_eq`: `finrank L A = finrank F K`.
* `GromovWitten.Algebra.finrank_sum_residueField`: if `K / F` is finite,
  `∑ p, finrank L κ(p) = finrank F K`.
* `GromovWitten.Algebra.norm_tensor_eq_prod`: if `K / F` is finite, for `a : K`,
  `algebraMap F L (N_{K/F} a) = ∏ p, N_{κ(p)/L} (image of a)`.
* `GromovWitten.Algebra.not_finite_residueField_of_not_finite`: if `K / F` is infinite, no
  residue field `κ(p)` is finite over `L`.
* `GromovWitten.Algebra.finrank_sum_residueField'`,
  `GromovWitten.Algebra.norm_tensor_eq_prod'`: the two identities above hold without any
  finiteness hypothesis on `K / F` (with Mathlib's conventions `finrank = 0` and `norm = 1`
  for infinite extensions).
-/

namespace GromovWitten.Algebra

open Module TensorProduct

/-- Auxiliary statement for `det_pi_dependent`, phrased for induction on the finite index type. -/
private theorem det_pi_dependent_aux {R : Type*} [CommRing R] (ι : Type*) [Finite ι] :
    ∀ [Fintype ι] (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
      [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)] (f : ∀ i, M i →ₗ[R] M i),
      (LinearMap.pi (fun i ↦ (f i).comp (LinearMap.proj i))).det = ∏ i, (f i).det := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
    rename_i α β
    intro _ M _ _ _ _ f
    let _ : Fintype α := Fintype.ofEquiv β e.symm
    have h := ih (fun a ↦ M (e a)) (fun a ↦ f (e a))
    let E := LinearEquiv.piCongrLeft R M e
    have hconj : LinearMap.pi (fun i ↦ (f i).comp (LinearMap.proj i)) =
        (E : _ →ₗ[R] _) ∘ₗ LinearMap.pi (fun a ↦ (f (e a)).comp (LinearMap.proj a)) ∘ₗ
          (E.symm : _ →ₗ[R] _) := by
      ext x b
      obtain ⟨a, rfl⟩ := e.surjective b
      change _ = Equiv.piCongrLeft M e _ (e a)
      rw [Equiv.piCongrLeft_apply_apply]
      rfl
    rw [hconj, LinearMap.det_conj, h]
    exact Fintype.prod_equiv e _ _ (fun _ ↦ rfl)
  | h_empty =>
    intro _ M _ _ _ _ f
    rw [LinearMap.det_eq_one_of_subsingleton]
    simp
  | h_option ih =>
    rename_i α _
    intro _ M _ _ _ _ f
    have h := ih (fun a ↦ M (some a)) (fun a ↦ f (some a))
    let E := LinearEquiv.piOptionEquivProd (R := R) (M := M)
    have hconj : LinearMap.pi (fun i ↦ (f i).comp (LinearMap.proj i)) =
        (E.symm : _ →ₗ[R] _) ∘ₗ ((f none).prodMap
          (LinearMap.pi (fun a ↦ (f (some a)).comp (LinearMap.proj a)))) ∘ₗ
          (E.symm.symm : _ →ₗ[R] _) := by
      ext x i
      cases i <;> rfl
    rw [hconj, LinearMap.det_conj, LinearMap.det_prodMap, h]
    convert (Fintype.prod_option (fun i ↦ (f i).det)).symm

/-- The determinant of the product endomorphism `∏ fᵢ` of `∀ i, M i`, for a finite family of
finite free modules `M i` (which may differ from each other), is the product of the
determinants of the `fᵢ`. Mathlib's `LinearMap.det_pi` is the special case of a constant
family. -/
theorem det_pi_dependent {R ι : Type*} [CommRing R] [Fintype ι] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, Module.Free R (M i)]
    [∀ i, Module.Finite R (M i)] (f : ∀ i, M i →ₗ[R] M i) :
    (LinearMap.pi (fun i ↦ (f i).comp (LinearMap.proj i))).det = ∏ i, (f i).det :=
  det_pi_dependent_aux ι M f

/-- The norm over a field `L` of an element of a finite product of finite `L`-algebras is the
product of the norms of its components. -/
theorem norm_pi_dependent {L ι : Type*} [Field L] [Fintype ι] (B : ι → Type*)
    [∀ i, CommRing (B i)] [∀ i, Algebra L (B i)] [∀ i, Module.Finite L (B i)]
    (x : ∀ i, B i) : Algebra.norm L x = ∏ i, Algebra.norm L (x i) := by
  rw [Algebra.norm_apply]
  have : Algebra.lmul L (∀ i, B i) x =
      LinearMap.pi (fun i ↦ (Algebra.lmul L (B i) (x i)).comp (LinearMap.proj i)) := by
    ext y i; rfl
  rw [this]
  exact det_pi_dependent B _

variable (F K L A : Type*) [Field F] [Field K] [Field L] [CommRing A]
  [Algebra F K] [Algebra F L] [Algebra F A] [Algebra K A] [Algebra L A]
  [IsScalarTower F K A] [IsScalarTower F L A] [Algebra.IsPushout F K L A]

include K in
/-- If `L / F` is finite separable and `A = K ⊗[F] L` (as a pushout), then `A` is reduced, for
any field extension `K` of `F`. -/
theorem isReduced_tensor [Algebra.IsSeparable F L] [Module.Finite F L] : IsReduced A := by
  have : Algebra.FormallyUnramified F L := Algebra.FormallyUnramified.of_isSeparable F L
  have : Algebra.EssFiniteType K (K ⊗[F] L) := inferInstance
  have : IsReduced (K ⊗[F] L) := Algebra.FormallyUnramified.isReduced_of_field K _
  exact isReduced_of_injective (Algebra.IsPushout.equiv F K L A).symm
    (Algebra.IsPushout.equiv F K L A).symm.injective

/-- If `L / F` is finite, then `A = K ⊗[F] L` is a finite `K`-module. -/
theorem module_finite_tensor [Module.Finite F L] : Module.Finite K A :=
  Module.Finite.equiv (Algebra.IsPushout.equiv F K L A).toLinearEquiv

include K in
/-- If `L / F` is finite, then `A = K ⊗[F] L` is an Artinian ring (whatever `K`), being finite
over the field `K`. -/
theorem isArtinianRing_tensor [Module.Finite F L] : IsArtinianRing A :=
  have := module_finite_tensor F K L A
  IsArtinianRing.of_finite K A

include K in
/-- If `L / F` is finite, then `A = K ⊗[F] L` has only finitely many prime ideals. -/
theorem finite_primeSpectrum_tensor [Module.Finite F L] : Finite (PrimeSpectrum A) :=
  have := isArtinianRing_tensor F K L A
  inferInstance

include K in
/-- If `L / F` is finite, then every prime ideal of `A = K ⊗[F] L` is maximal. -/
theorem isMaximal_of_isPrime_tensor [Module.Finite F L] (p : Ideal A) [p.IsPrime] :
    p.IsMaximal :=
  have := isArtinianRing_tensor F K L A
  IsArtinianRing.isMaximal_of_isPrime p

/-- If `L / F` is finite, then `finrank L (K ⊗[F] L) = finrank F K` (both sides are `0` when
`K / F` is infinite). -/
theorem finrank_tensor_eq [Module.Finite F L] : finrank L A = finrank F K := by
  have : Algebra.IsPushout F L K A := Algebra.IsPushout.symm inferInstance
  rw [← (Algebra.IsPushout.equiv F L K A).toLinearEquiv.finrank_eq, Module.finrank_baseChange]

/-- For a maximal ideal `p` of an `L`-algebra `A`, the residue field `κ(p)` and the quotient
`A ⧸ p` have the same dimension over `L`. -/
theorem finrank_residueField_eq_quotient (p : Ideal A) [p.IsMaximal] :
    finrank L p.ResidueField = finrank L (A ⧸ p) :=
  (LinearEquiv.ofBijective (IsScalarTower.toAlgHom L (A ⧸ p) p.ResidueField).toLinearMap
    p.bijective_algebraMap_quotient_residueField).finrank_eq.symm

/-- For a maximal ideal `p` of an `L`-algebra `A` and `x : A`, the norm over `L` of the image of
`x` in the residue field `κ(p)` equals the norm over `L` of its image in `A ⧸ p`. -/
theorem norm_residueField_eq_quotient (p : Ideal A) [p.IsMaximal] (x : A) :
    Algebra.norm L (algebraMap A p.ResidueField x) = Algebra.norm L (Ideal.Quotient.mk p x) := by
  rw [← Ideal.algebraMap_quotient_residueField_mk]
  exact Algebra.norm_eq_of_algEquiv
    (AlgEquiv.ofBijective (IsScalarTower.toAlgHom L (A ⧸ p) p.ResidueField)
      p.bijective_algebraMap_quotient_residueField) (Ideal.Quotient.mk p x)

/-- If `L / F` is finite separable and `K / F` is finite, then for `A = K ⊗[F] L`,
`∑ p : PrimeSpectrum A, finrank L κ(p) = finrank F K`, where `κ(p)` is an `L`-algebra through
`A`. -/
theorem finrank_sum_residueField [Algebra.IsSeparable F L] [Module.Finite F L]
    [Module.Finite F K] [Fintype (PrimeSpectrum A)] :
    ∑ p : PrimeSpectrum A, finrank L p.asIdeal.ResidueField = finrank F K := by
  classical
  have := isArtinianRing_tensor F K L A
  have := isReduced_tensor F K L A
  have : Module.Finite L A := by
    have : Algebra.IsPushout F L K A := Algebra.IsPushout.symm inferInstance
    exact Module.Finite.equiv (Algebra.IsPushout.equiv F L K A).toLinearEquiv
  let _ : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  let e := ((IsArtinianRing.equivPi A).restrictScalars L).toLinearEquiv
  rw [← finrank_tensor_eq F K L A, e.finrank_eq, Module.finrank_pi_fintype]
  refine Fintype.sum_equiv (IsArtinianRing.primeSpectrumEquivMaximalSpectrum (R := A)) _ _ ?_
  intro p
  exact finrank_residueField_eq_quotient L A p.asIdeal

/-- Norms commute with base change: if `K / F` is finite and `A = K ⊗[F] L` (here `L` is any
field extension of `F`), then `algebraMap F L (N_{K/F} a) = N_{A/L} (a ⊗ 1)` for `a : K`. -/
theorem algebraMap_norm_eq_norm_tensor [Module.Finite F K] (a : K) :
    algebraMap F L (Algebra.norm F a) = Algebra.norm L (algebraMap K A a) := by
  have : Algebra.IsPushout F L K A := Algebra.IsPushout.symm inferInstance
  have h : Algebra.IsPushout.equiv F L K A (1 ⊗ₜ a) = algebraMap K A a := by
    rw [Algebra.IsPushout.equiv_tmul, map_one, one_mul]
  rw [← h, Algebra.norm_eq_of_algEquiv, Algebra.norm_apply, Algebra.norm_apply,
    ← Algebra.baseChange_lmul, LinearMap.det_baseChange]

/-- If `L / F` is finite separable and `K / F` is finite, then for `A = K ⊗[F] L` and `a : K`,
`algebraMap F L (N_{K/F} a) = ∏ p : PrimeSpectrum A, N_{κ(p)/L} (image of a in κ(p))`. -/
theorem norm_tensor_eq_prod [Algebra.IsSeparable F L] [Module.Finite F L]
    [Module.Finite F K] [Fintype (PrimeSpectrum A)] (a : K) :
    algebraMap F L (Algebra.norm F a) =
      ∏ p : PrimeSpectrum A, Algebra.norm L (algebraMap A p.asIdeal.ResidueField
        (algebraMap K A a)) := by
  classical
  have := isArtinianRing_tensor F K L A
  have := isReduced_tensor F K L A
  have : Module.Finite L A := by
    have : Algebra.IsPushout F L K A := Algebra.IsPushout.symm inferInstance
    exact Module.Finite.equiv (Algebra.IsPushout.equiv F L K A).toLinearEquiv
  let _ : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  let e := (IsArtinianRing.equivPi A).restrictScalars L
  rw [algebraMap_norm_eq_norm_tensor F K L A, ← Algebra.norm_eq_of_algEquiv e,
    norm_pi_dependent]
  refine (Fintype.prod_equiv (IsArtinianRing.primeSpectrumEquivMaximalSpectrum (R := A)) _ _
    ?_).symm
  intro p
  exact norm_residueField_eq_quotient L A p.asIdeal _

omit [Algebra.IsPushout F K L A] in
/-- If `L / F` is finite and `K / F` is infinite, then for every prime `p` of the
`K`-algebra-and-`L`-algebra `A` (no pushout hypothesis is needed), the residue field `κ(p)` is
not finite over `L`. -/
theorem not_finite_residueField_of_not_finite [Module.Finite F L] (hK : ¬ Module.Finite F K)
    (p : PrimeSpectrum A) : ¬ Module.Finite L p.asIdeal.ResidueField := by
  intro hp
  have : Module.Finite F p.asIdeal.ResidueField := Module.Finite.trans L _
  let g : K →ₐ[F] p.asIdeal.ResidueField :=
    (IsScalarTower.toAlgHom F A p.asIdeal.ResidueField).comp (IsScalarTower.toAlgHom F K A)
  exact hK (FiniteDimensional.of_injective g.toLinearMap g.toRingHom.injective)

/-- The identity `∑ p : PrimeSpectrum A, finrank L κ(p) = finrank F K` for `A = K ⊗[F] L`,
with `L / F` finite separable and no finiteness hypothesis on `K / F` (when `K / F` is infinite
both sides are `0`). -/
theorem finrank_sum_residueField' [Algebra.IsSeparable F L] [Module.Finite F L]
    [Fintype (PrimeSpectrum A)] :
    ∑ p : PrimeSpectrum A, finrank L p.asIdeal.ResidueField = finrank F K := by
  by_cases hK : Module.Finite F K
  · exact finrank_sum_residueField F K L A
  · rw [finrank_of_not_finite hK]
    exact Finset.sum_eq_zero fun p _ ↦
      finrank_of_not_finite (not_finite_residueField_of_not_finite F K L A hK p)

/-- The identity `algebraMap F L (N_{K/F} a) = ∏ p, N_{κ(p)/L} (image of a)` for
`A = K ⊗[F] L`, with `L / F` finite separable and no finiteness hypothesis on `K / F` (when
`K / F` is infinite both sides are `1`). -/
theorem norm_tensor_eq_prod' [Algebra.IsSeparable F L] [Module.Finite F L]
    [Fintype (PrimeSpectrum A)] (a : K) :
    algebraMap F L (Algebra.norm F a) =
      ∏ p : PrimeSpectrum A, Algebra.norm L (algebraMap A p.asIdeal.ResidueField
        (algebraMap K A a)) := by
  by_cases hK : Module.Finite F K
  · exact norm_tensor_eq_prod F K L A a
  · rw [Algebra.norm_eq_one_of_not_module_finite hK, map_one]
    exact (Finset.prod_eq_one fun p _ ↦ Algebra.norm_eq_one_of_not_module_finite
      (not_finite_residueField_of_not_finite F K L A hK p) _).symm

end GromovWitten.Algebra
