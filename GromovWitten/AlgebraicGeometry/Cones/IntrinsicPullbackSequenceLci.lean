/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/

import GromovWitten.AlgebraicGeometry.Cones.IntrinsicPullbackSequence
import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.LciFormulaPure
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.TensorProduct.Free

/-!
# The intrinsic pullback sequence for a quasi-regular (lci) tower

`Cones/IntrinsicPullbackSequence.lean` proves the Jacobi–Zariski sequence of two-term
presentation complexes attached to a tower `R → S → T` is short exact
(`PicardCriteria.shortExact_jz`) as soon as the conormal comparison map

`(jzToComp Q P).degreeZero : T ⊗[S] P.toExtension.Cotangent → (Q.comp P).toExtension.Cotangent`

is injective, and `ObstructionTheory/DerivedInvariance.lean` discharges this hypothesis when `S`
is formally smooth over `R` and `T` is flat over `S`.  This file discharges the same hypothesis
for the complementary, *local complete intersection* case: `S/R` and `T/R` both admit a
quasi-regular (lci) presentation, and the chosen presentation of `T/R` extends the chosen
presentation of `S/R`.

## Main results

* `hcompat_basisOfQuasiregular`, `shortExact_jz_of_quasiregular_generators`,
  `shortExact_dual_jz_of_quasiregular_generators`,
  `shortExactPicard_dual_jz_of_quasiregular_generators`: **the headline results — the lci
  intrinsic pullback sequence, stated directly from a compatible pair of quasi-regular
  sequences.**  Given a quasi-regular sequence `x` for `S/R` and a quasi-regular sequence `y` for
  `T/R` (via the composite presentation `Q.comp P`) whose classes extend `x`'s along an injective
  reindexing `e` (`y.gen (e i)` is the image of `x.gen i` under the inclusion of ambient
  polynomial rings, `MvPolynomial.rename Sum.inr`), the Jacobi–Zariski sequence of `R → S → T` is
  unconditionally short exact from this data alone — no flatness hypothesis on `T/S` is needed; a
  further quasi-regular sequence `z` for `T/S` (discharging `hproj` via
  `Module.Free.of_basis (basisOfQuasiregular Q z)`) upgrades this to the full intrinsic pullback
  sequence of Picard groupoids.
* `basisOfQuasiregular`: the concrete ingredient behind the headline results.  Given
  `x : AffineNormalCone.QuasiregularGenerators P.Ring (Algebra.Generators.ker P)`,
  `basisOfQuasiregular P x` is the basis of `P.toExtension.Cotangent` over `S` obtained by
  transporting `x.cotangentBasis` — a basis of `Ideal.Cotangent (Algebra.Generators.ker P)` over
  the quotient ring `P.Ring ⁄ Algebra.Generators.ker P` — along the designated section `P.σ`,
  which identifies that quotient ring with `S` (`injective_quotientMk_sigma`,
  `surjective_quotientMk_sigma`).
* `injective_jzToComp_degreeZero_of_quasiregular`, `shortExact_jz_of_quasiregular`,
  `shortExactPicard_dual_jz_of_quasiregular`, `shortExact_dual_jz_of_quasiregular`: the internal,
  more general *compatible-bases* form from which the headline results above are discharged (via
  `basisOfQuasiregular` and `hcompat_basisOfQuasiregular`).  If the conormal modules of the
  presentations of `S/R` and of `T/R` (with `T/R`'s presentation the pushout `Q.comp P` of `T/S`'s
  along `S/R`'s) have compatible bases — a basis `b` of `P.toExtension.Cotangent` over `S` and a
  basis `b'` of `(Q.comp P).toExtension.Cotangent` over `T` together with an injective reindexing
  `e` along which `(jzToComp Q P).degreeZero` carries `b` (base-changed to `T`) into `b'` — then
  `(jzToComp Q P).degreeZero` is injective, giving the lci counterparts of
  `PicardCriteria.shortExact_jz_of_flat`/`shortExact_dual_jz_of_smooth`/
  `shortExactPicard_dual_jz_of_smooth` under this hypothesis together with freeness of the
  relative conormal module `Q.toExtension.Cotangent` (discharging `hproj`).

## Why "`T` flat over `S`" is not the hypothesis used here

Plain flatness of `T` over `S` is the hypothesis that works in the smooth case
(`injective_jzToComp_degreeZero_of_flat`).  The proof strategy attempted in this file — realizing
`hinj` as "a linear map out of a free module is injective as soon as it carries some basis to a
linearly independent family" (`LinearMap.injective_of_linearIndependent`), applied to the basis of
`P.toExtension.Cotangent` coming from a quasi-regular sequence for `S/R` and a basis of
`(Q.comp P).toExtension.Cotangent` coming from a quasi-regular sequence for `T/R` — needs the
*second* sequence to extend the first, which is data beyond quasi-regularity of `S/R` and
flatness of `T/S`: quasi-regularity of `I` plus flatness of `T` over `S` was not enough for the
proof strategy attempted here, which needs a compatible pair of generating sequences; whether
`hinj` can fail under those hypotheses alone (with no compatible pair available) is not settled in
this file.
-/

open CategoryTheory TensorProduct

universe u

namespace GromovWitten.AlgebraicGeometry

namespace PicardCriteria

open LinearTwoTermComplex CotangentComplex

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable {ι σ : Type u} {κ κ' : Type*} (Q : Algebra.Generators.{u} S T ι)
  (P : Algebra.Generators.{u} R S σ)

/-! ## Injectivity of the conormal comparison from a pair of compatible bases -/

/-- **The conormal map of the Jacobi–Zariski sequence is injective** when the conormal modules
of the presentations of `S/R` and of `T/R` have compatible bases.  A linear map out of a free
module is injective as soon as it carries a basis to a linearly independent family
(`LinearMap.injective_of_linearIndependent`); the base-changed basis `1 ⊗ b` of
`T ⊗[S] P.toExtension.Cotangent` (`Algebra.TensorProduct.basis`) is carried, by hypothesis, to
the sub-family `b' ∘ e` of the basis `b'`, which is linearly independent because `e` is
injective. -/
theorem injective_jzToComp_degreeZero_of_quasiregular
    (b : Module.Basis κ S P.toExtension.Cotangent)
    (b' : Module.Basis κ' T (Q.comp P).toExtension.Cotangent)
    (e : κ → κ') (he : Function.Injective e)
    (hcompat : ∀ i, (jzToComp Q P).degreeZero (1 ⊗ₜ[S] b i) = b' (e i)) :
    Function.Injective (jzToComp Q P).degreeZero := by
  refine LinearMap.injective_of_linearIndependent
    (v := Algebra.TensorProduct.basis T b) (Module.Basis.span_eq _) ?_
  have hfun : (jzToComp Q P).degreeZero ∘ (Algebra.TensorProduct.basis T b) = b' ∘ e := by
    funext i
    change (jzToComp Q P).degreeZero (Algebra.TensorProduct.basis T b i) = b' (e i)
    rw [Algebra.TensorProduct.basis_apply]
    exact hcompat i
  rw [hfun]
  exact b'.linearIndependent.comp e he

/-- **The Jacobi–Zariski sequence of two-term complexes is short exact** for a tower whose
conormal modules have compatible bases: hypothesis (i) of `shortExact_jz` is discharged by
`injective_jzToComp_degreeZero_of_quasiregular`. -/
theorem shortExact_jz_of_quasiregular
    (b : Module.Basis κ S P.toExtension.Cotangent)
    (b' : Module.Basis κ' T (Q.comp P).toExtension.Cotangent)
    (e : κ → κ') (he : Function.Injective e)
    (hcompat : ∀ i, (jzToComp Q P).degreeZero (1 ⊗ₜ[S] b i) = b' (e i)) :
    ShortExact (jzToComp Q P) (jzOfComp Q P) :=
  shortExact_jz Q P (injective_jzToComp_degreeZero_of_quasiregular Q P b b' e he hcompat)

/-- **The intrinsic pullback sequence is unconditional under the compatible-basis hypothesis,
for `T/S` local complete intersection.**  If, in addition to a pair of compatible bases for the
presentations of `S/R` and `T/R`, the relative conormal module `Q.toExtension.Cotangent` of
`T/S` is free — the lci hypothesis on `T/S` itself, e.g. from a quasi-regular sequence for `T/S`
— both hypotheses of `shortExactPicard_dual_jz` hold. -/
theorem shortExactPicard_dual_jz_of_quasiregular
    (b : Module.Basis κ S P.toExtension.Cotangent)
    (b' : Module.Basis κ' T (Q.comp P).toExtension.Cotangent)
    (e : κ → κ') (he : Function.Injective e)
    (hcompat : ∀ i, (jzToComp Q P).degreeZero (1 ⊗ₜ[S] b i) = b' (e i))
    [Module.Free T Q.toExtension.Cotangent] (B : Type u) [CommRing B] [Algebra T B] :
    ShortExactPicard (dualHom (jzOfComp Q P) B) (dualHom (jzToComp Q P) B) :=
  shortExactPicard_dual_jz Q P B
    (injective_jzToComp_degreeZero_of_quasiregular Q P b b' e he hcompat)
    Module.Projective.of_free

/-- The same in the form of a short exact sequence of two-term complexes of `B`-points. -/
theorem shortExact_dual_jz_of_quasiregular
    (b : Module.Basis κ S P.toExtension.Cotangent)
    (b' : Module.Basis κ' T (Q.comp P).toExtension.Cotangent)
    (e : κ → κ') (he : Function.Injective e)
    (hcompat : ∀ i, (jzToComp Q P).degreeZero (1 ⊗ₜ[S] b i) = b' (e i))
    [Module.Free T Q.toExtension.Cotangent] (B : Type u) [CommRing B] [Algebra T B] :
    ShortExact (dualHom (jzOfComp Q P) B) (dualHom (jzToComp Q P) B) :=
  shortExact_dual_jz Q P B
    (injective_jzToComp_degreeZero_of_quasiregular Q P b b' e he hcompat)
    Module.Projective.of_free

/-! ## Bases from quasi-regular generators -/

section QuasiregularBasis

variable {ρ : Type u} (P' : Algebra.Generators.{u} R S ρ)

/-- The designated section of a presentation, followed by reduction modulo the kernel, is
injective: this is the elementary content of the first isomorphism theorem for the surjection
`aeval P'.val : P'.Ring → S` underlying the presentation. -/
theorem injective_quotientMk_sigma :
    Function.Injective fun r : S => Ideal.Quotient.mk (Algebra.Generators.ker P') (P'.σ r) := by
  intro r r' h
  rw [Ideal.Quotient.eq, Algebra.Generators.ker_eq_ker_aeval_val, RingHom.mem_ker, map_sub] at h
  simp only [Algebra.Generators.aeval_val_σ] at h
  exact sub_eq_zero.mp h

/-- The image of `0` under the designated section, reduced modulo the kernel, is `0`: a special
case of `injective_quotientMk_sigma`'s proof, recorded separately for use with
`Function.Injective`. -/
theorem quotientMk_sigma_zero :
    Ideal.Quotient.mk (Algebra.Generators.ker P') (P'.σ (0 : S)) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Algebra.Generators.ker_eq_ker_aeval_val, RingHom.mem_ker,
    Algebra.Generators.aeval_val_σ]

/-- The designated section of a presentation, followed by reduction modulo the kernel, is
surjective: given `a : P'.Ring`, the class of `P'.σ (aeval P'.val a)` modulo the kernel equals
the class of `a`, since the two differ by an element killed by `aeval P'.val`. -/
theorem surjective_quotientMk_sigma :
    Function.Surjective fun r : S => Ideal.Quotient.mk (Algebra.Generators.ker P') (P'.σ r) := by
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := Algebra.Generators.ker P') a
  refine ⟨MvPolynomial.aeval P'.val a, ?_⟩
  rw [Ideal.Quotient.eq, Algebra.Generators.ker_eq_ker_aeval_val, RingHom.mem_ker, map_sub,
    Algebra.Generators.aeval_val_σ, sub_self]

/-- The identity `Algebra.Extension.Cotangent.val` as a bundled additive homomorphism, so that
`map_sum` applies to it.  (`Algebra.Generators.ker P'` and the kernel `P'.toExtension.ker` of the
extension underlying `Algebra.Extension.Cotangent` are equal by the `abbrev` defining `ker`, but
not reducibly so for `rw`'s keyed matching; every genuine use of that equality below goes through
`rfl`/definitional unfolding instead, which sees through it.) -/
noncomputable def cotangentValHom : P'.toExtension.Cotangent →+ P'.toExtension.ker.Cotangent where
  toFun := Algebra.Extension.Cotangent.val
  map_zero' := rfl
  map_add' _ _ := rfl

open AffineNormalCone in
/-- **A basis of the conormal module of a presentation from a quasi-regular sequence
generating its kernel.**  Transports `QuasiregularGenerators.cotangentBasis` (a basis of
`Ideal.Cotangent (Algebra.Generators.ker P')` over `P'.Ring ⁄ Algebra.Generators.ker P'`) along
the identification `Algebra.Extension.Cotangent.val` of `P'.toExtension.Cotangent` with that
module, using that the designated section `P'.σ`, reduced modulo the kernel, is a two-sided
inverse of the canonical isomorphism `P'.Ring ⁄ Algebra.Generators.ker P' ≃ S`
(`injective_quotientMk_sigma`, `surjective_quotientMk_sigma`) intertwining the two module
structures — the key computation, that `(Ideal.Quotient.mk _ (P'.σ r)) • y` and
`Algebra.Extension.Cotangent.val (r • Algebra.Extension.Cotangent.of y)` agree, holds by `rfl`
(`Algebra.Extension.Cotangent.val_smul` composed with `Module.IsTorsionBySet.mk_smul`, both
themselves proved by `rfl` in Mathlib). -/
noncomputable def basisOfQuasiregular
    (x : QuasiregularGenerators P'.Ring (Algebra.Generators.ker P')) :
    Module.Basis (Fin x.length) S P'.toExtension.Cotangent := by
  refine Module.Basis.mk (v := fun i => Algebra.Extension.Cotangent.of (x.conormalGen i)) ?_ ?_
  · rw [Fintype.linearIndependent_iff]
    intro c hc j
    have heq : ∀ i, (Ideal.Quotient.mk (Algebra.Generators.ker P') (P'.σ (c i))) •
        x.conormalGen i = cotangentValHom P'
          (c i • Algebra.Extension.Cotangent.of (x.conormalGen i)) := fun i => rfl
    have hval := congrArg (cotangentValHom P') hc
    rw [map_sum, map_zero] at hval
    have hval2 : ∑ i, (Ideal.Quotient.mk (Algebra.Generators.ker P') (P'.σ (c i))) •
        x.conormalGen i = (0 : P'.ker.Cotangent) :=
      (Finset.sum_congr rfl fun i _ => heq i).trans hval
    have hz := (Fintype.linearIndependent_iff.mp x.linearIndependent_conormalGen)
      (fun i => Ideal.Quotient.mk (Algebra.Generators.ker P') (P'.σ (c i))) hval2 j
    exact injective_quotientMk_sigma P' (hz.trans (quotientMk_sigma_zero P').symm)
  · rw [Submodule.top_le_span_range_iff_forall_exists_fun (R := S)]
    intro m
    let mval : P'.ker.Cotangent := m.val
    have hspan : mval ∈ Submodule.span (P'.Ring ⧸ Algebra.Generators.ker P')
        (Set.range x.conormalGen) := x.span_range_conormalGen ▸ Submodule.mem_top
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun
      (R := P'.Ring ⧸ Algebra.Generators.ker P')).mp hspan
    choose r hr using fun i => surjective_quotientMk_sigma P' (d i)
    refine ⟨r, Algebra.Extension.Cotangent.ext ?_⟩
    have heq : ∀ i, cotangentValHom P'
        (r i • Algebra.Extension.Cotangent.of (x.conormalGen i)) =
        (Ideal.Quotient.mk (Algebra.Generators.ker P') (P'.σ (r i))) • x.conormalGen i :=
      fun i => rfl
    change cotangentValHom P' (∑ i, r i • Algebra.Extension.Cotangent.of (x.conormalGen i)) = mval
    rw [map_sum]
    rw [show (∑ i, cotangentValHom P'
        (r i • Algebra.Extension.Cotangent.of (x.conormalGen i))) =
        ∑ i, (Ideal.Quotient.mk (Algebra.Generators.ker P') (P'.σ (r i))) • x.conormalGen i from
      Finset.sum_congr rfl fun i _ => heq i]
    simp_rw [hr]
    exact hd

open AffineNormalCone in
@[simp]
theorem basisOfQuasiregular_apply
    (x : QuasiregularGenerators P'.Ring (Algebra.Generators.ker P')) (i : Fin x.length) :
    basisOfQuasiregular P' x i = Algebra.Extension.Cotangent.of (x.conormalGen i) :=
  Module.Basis.mk_apply _ _ i

end QuasiregularBasis

/-! ## The lci intrinsic pullback sequence, from generators -/

section GeneratorsWiring

open AffineNormalCone

variable {ι σ : Type u} (Q : Algebra.Generators.{u} S T ι) (P : Algebra.Generators.{u} R S σ)

/-- **The bases of `basisOfQuasiregular` are compatible along `jzToComp`** when the quasi-regular
generators of the composite presentation `Q.comp P` extend those of `P` along the natural
inclusion `P.Ring → (Q.comp P).Ring` (`Algebra.Generators.toComp_toAlgHom` identifies it with
`MvPolynomial.rename Sum.inr`). This is exactly hypothesis `hcompat` of
`injective_jzToComp_degreeZero_of_quasiregular`, verified by unwinding `jzToComp`'s definition
(`LinearMap.liftBaseChange_one_tmul`) and the computation rule `Algebra.Extension.Cotangent.map_mk`
of `Cotangent.map` on the class of a generator. -/
theorem hcompat_basisOfQuasiregular
    (x : QuasiregularGenerators P.Ring (Algebra.Generators.ker P))
    (y : QuasiregularGenerators (Q.comp P).Ring (Algebra.Generators.ker (Q.comp P)))
    (e : Fin x.length → Fin y.length)
    (hgen : ∀ i, y.gen (e i) = MvPolynomial.rename Sum.inr (x.gen i)) (i : Fin x.length) :
    (jzToComp Q P).degreeZero (1 ⊗ₜ[S] basisOfQuasiregular P x i) =
      basisOfQuasiregular (Q.comp P) y (e i) := by
  rw [basisOfQuasiregular_apply, basisOfQuasiregular_apply]
  change (Algebra.Extension.Cotangent.map (Q.toComp P).toExtensionHom).liftBaseChange T
    (1 ⊗ₜ[S] Algebra.Extension.Cotangent.of (x.conormalGen i)) =
    Algebra.Extension.Cotangent.of (y.conormalGen (e i))
  rw [LinearMap.liftBaseChange_one_tmul]
  change Algebra.Extension.Cotangent.map (Q.toComp P).toExtensionHom
    (Algebra.Extension.Cotangent.mk (x.genMem i)) =
    Algebra.Extension.Cotangent.mk (y.genMem (e i))
  refine (Algebra.Extension.Cotangent.map_mk (Q.toComp P).toExtensionHom (x.genMem i)).trans ?_
  congr 1
  refine Subtype.ext ?_
  change (Q.toComp P).toAlgHom (x.gen i) = y.gen (e i)
  rw [Algebra.Generators.toComp_toAlgHom, hgen]

/-- **The lci intrinsic pullback sequence, from a compatible pair of quasi-regular
sequences.**  If `x` is a quasi-regular sequence generating the kernel of the presentation `P`
of `S/R`, and `y` is a quasi-regular sequence generating the kernel of the composite presentation
`Q.comp P` of `T/R` whose classes, reindexed along an injection `e`, extend those of `x` (in the
sense that `y.gen (e i)` is the image of `x.gen i` under the natural inclusion of ambient
polynomial rings), then the Jacobi–Zariski sequence of `R → S → T` is short exact: hypothesis
`hinj` of `PicardCriteria.shortExact_jz` is discharged unconditionally from this data (no
flatness hypothesis on `T/S` is needed). -/
theorem shortExact_jz_of_quasiregular_generators
    (x : QuasiregularGenerators P.Ring (Algebra.Generators.ker P))
    (y : QuasiregularGenerators (Q.comp P).Ring (Algebra.Generators.ker (Q.comp P)))
    (e : Fin x.length → Fin y.length) (he : Function.Injective e)
    (hgen : ∀ i, y.gen (e i) = MvPolynomial.rename Sum.inr (x.gen i)) :
    ShortExact (jzToComp Q P) (jzOfComp Q P) := by
  let hb := basisOfQuasiregular P x
  let hb' := basisOfQuasiregular (Q.comp P) y
  exact shortExact_jz_of_quasiregular Q P hb hb' e he
    (hcompat_basisOfQuasiregular Q P x y e hgen)

variable (B : Type u) [CommRing B] [Algebra T B]

/-- **The intrinsic pullback sequence, from a compatible pair of quasi-regular sequences for
`S/R` and `T/R`, together with a quasi-regular sequence for `T/S` itself.**  The last hypothesis
(`z`, discharging `hproj` via `Module.Free.of_basis (basisOfQuasiregular Q z)`) is exactly the
local-complete-intersection hypothesis on `T/S`: this is the lci case of
`ObstructionTheory.DerivedInvariance.shortExact_dual_jz_of_smooth`. -/
theorem shortExact_dual_jz_of_quasiregular_generators
    (x : QuasiregularGenerators P.Ring (Algebra.Generators.ker P))
    (y : QuasiregularGenerators (Q.comp P).Ring (Algebra.Generators.ker (Q.comp P)))
    (e : Fin x.length → Fin y.length) (he : Function.Injective e)
    (hgen : ∀ i, y.gen (e i) = MvPolynomial.rename Sum.inr (x.gen i))
    (z : QuasiregularGenerators Q.Ring (Algebra.Generators.ker Q)) :
    ShortExact (dualHom (jzOfComp Q P) B) (dualHom (jzToComp Q P) B) := by
  have : Module.Free T Q.toExtension.Cotangent := Module.Free.of_basis (basisOfQuasiregular Q z)
  let hb := basisOfQuasiregular P x
  let hb' := basisOfQuasiregular (Q.comp P) y
  exact shortExact_dual_jz_of_quasiregular Q P hb hb' e he
    (hcompat_basisOfQuasiregular Q P x y e hgen) B

/-- The Picard-groupoid form of `shortExact_dual_jz_of_quasiregular_generators`. -/
theorem shortExactPicard_dual_jz_of_quasiregular_generators
    (x : QuasiregularGenerators P.Ring (Algebra.Generators.ker P))
    (y : QuasiregularGenerators (Q.comp P).Ring (Algebra.Generators.ker (Q.comp P)))
    (e : Fin x.length → Fin y.length) (he : Function.Injective e)
    (hgen : ∀ i, y.gen (e i) = MvPolynomial.rename Sum.inr (x.gen i))
    (z : QuasiregularGenerators Q.Ring (Algebra.Generators.ker Q)) :
    ShortExactPicard (dualHom (jzOfComp Q P) B) (dualHom (jzToComp Q P) B) :=
  (shortExact_dual_jz_of_quasiregular_generators Q P B x y e he hgen z).shortExactPicard

end GeneratorsWiring

end PicardCriteria

end GromovWitten.AlgebraicGeometry
