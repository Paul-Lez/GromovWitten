/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.Algebra.FlatDescentModule
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Etale.Descent

/-!
# Effective flat descent of algebras (cocycle form)

Let `A → B` be a map of commutative rings and `M` a commutative `B`-algebra (hence an `A`-algebra
through `IsScalarTower A B M`).  An *algebra descent datum* on `M`,
`GromovWitten.Algebra.AlgDescentDatum`, `extends` a module descent datum
`GromovWitten.Algebra.DescentDatum` (file `FlatDescentModule.lean`, so it carries `τ`, `τ_smul`,
`cocycle`, `bijective` unchanged) with an `A`-algebra homomorphism
`τₐ : M →ₐ[A] B ⊗[A] M` and a proof `τ_eq : τ = τₐ.toLinearMap` that `τₐ` is the algebra lift of
the inherited coaction `τ`; semilinearity of `τₐ` itself is then derived as the simp lemma
`τₐ_smul`.  We show that the descended `A`-submodule `toDescentDatum.descended` of `M` is in fact
an `A`-subalgebra `descendedAlgebra`, that `B ⊗[A] descendedAlgebra ≃ₐ[B] M`, and that (under
faithful flatness) finiteness, finite type, finite presentation and étaleness of `M` over `B`
descend to `descendedAlgebra` over `A`.

## Main results

* `GromovWitten.Algebra.AlgDescentDatum`: an algebra descent datum on a `B`-algebra `M`,
  extending `GromovWitten.Algebra.DescentDatum` with the algebra lift `τₐ` of its coaction.
* `GromovWitten.Algebra.AlgDescentDatum.τₐ_smul`: semilinearity of `τₐ` for the left `B`-action,
  derived from the inherited field `τ_smul`.
* `GromovWitten.Algebra.AlgDescentDatum.descendedAlgebra`: the descended `A`-subalgebra of `M`.
* `GromovWitten.Algebra.AlgDescentDatum.descendedAlgebra_toSubmodule`: its underlying submodule
  is the descended module `toDescentDatum.descended`.
* `GromovWitten.Algebra.AlgDescentDatum.descentAlgEquiv`: for `B` flat over `A`,
  `B ⊗[A] descendedAlgebra ≃ₐ[B] M` (effective descent of algebras).
* `GromovWitten.Algebra.AlgDescentDatum.descentAlgEquiv_tmul`: `descentAlgEquiv (b ⊗ n) = b • n`.
* `GromovWitten.Algebra.AlgDescentDatum.finite_descendedAlgebra`,
  `finiteType_descendedAlgebra`, `finitePresentation_descendedAlgebra`,
  `etale_descendedAlgebra`: under `[Module.FaithfullyFlat A B]`, finiteness / finite type /
  finite presentation / étaleness of `M` over `B` descends to `descendedAlgebra` over `A`.
* `GromovWitten.Algebra.AlgDescentDatum.canonical`: the canonical algebra descent datum on
  `B ⊗[A] N` for an `A`-algebra `N`.
* `GromovWitten.Algebra.AlgDescentDatum.includeRight_mem_descendedAlgebra_canonical`: `N`
  (embedded by `n ↦ 1 ⊗ n`) lies in the descended algebra of the canonical datum.
-/

open TensorProduct

namespace GromovWitten.Algebra

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
variable (M : Type*) [CommRing M] [Algebra B M] [Algebra A M] [IsScalarTower A B M]

/-- An algebra descent datum (in `τ`-form) on a commutative `B`-algebra `M` relative to `A → B`:
a module descent datum (`τ`, `τ_smul`, `cocycle`, `bijective`, as in `DescentDatum`) together with
an `A`-algebra homomorphism `τₐ : M →ₐ[A] B ⊗[A] M` lifting the coaction `τ`, i.e.
`τ = τₐ.toLinearMap`. -/
structure AlgDescentDatum extends DescentDatum A B M where
  /-- The coaction `τₐ : M → B ⊗[A] M`, as an `A`-algebra homomorphism lifting `τ`. -/
  τₐ : M →ₐ[A] B ⊗[A] M
  /-- `τₐ` lifts the inherited coaction `τ`. -/
  τ_eq : τ = τₐ.toLinearMap

namespace AlgDescentDatum

variable {A B M}
variable (D : AlgDescentDatum A B M)

/-- Semilinearity of `τₐ` for the left `B`-action, derived from the inherited field `τ_smul`. -/
@[simp]
lemma τₐ_smul (b : B) (m : M) : D.τₐ (b • m) = b • D.τₐ m := by
  have h := D.τ_smul b m
  rwa [D.τ_eq] at h

/-- The cocycle condition for `τₐ`, derived from the inherited field `cocycle`. -/
lemma τₐ_cocycle (m : M) : LinearMap.lTensor B D.τₐ.toLinearMap (D.τₐ m) =
    TensorProduct.assoc A B B M (LinearMap.rTensor M (descentInsLeft A B) (D.τₐ m)) := by
  have h := D.cocycle m
  rwa [D.τ_eq] at h

/-- The associated map `M ⊗[A] B → B ⊗[A] M` of `τₐ` is bijective, derived from the inherited
field `bijective`. -/
lemma τₐ_bijective : Function.Bijective (descentToPhi A B M D.τₐ.toLinearMap) := by
  have h := D.bijective
  rwa [D.τ_eq] at h

/-- **Theorem F2.a** (descended module is a subalgebra). The descended `A`-subalgebra of `M`:
the equalizer of `τₐ` and `Algebra.TensorProduct.includeRight`, i.e.
`{m | τₐ m = 1 ⊗ m}`. -/
def descendedAlgebra : Subalgebra A M :=
  AlgHom.equalizer D.τₐ (Algebra.TensorProduct.includeRight : M →ₐ[A] B ⊗[A] M)

lemma mem_descendedAlgebra_iff (m : M) :
    m ∈ D.descendedAlgebra ↔ D.τₐ m = (1 : B) ⊗ₜ[A] m :=
  Iff.rfl

@[simp]
lemma toDescentDatum_τ : D.toDescentDatum.τ = D.τ := rfl

/-- The underlying `A`-submodule of `descendedAlgebra` is the descended module of the underlying
module descent datum. -/
theorem descendedAlgebra_toSubmodule :
    D.descendedAlgebra.toSubmodule = D.toDescentDatum.descended := by
  ext m
  simp only [Subalgebra.mem_toSubmodule, D.mem_descendedAlgebra_iff,
    DescentDatum.mem_descended_iff, D.τ_eq, AlgHom.toLinearMap_apply]

/-- The canonical `A`-linear equivalence between `descendedAlgebra` (as a module) and the
descended module `toDescentDatum.descended`. -/
noncomputable def descendedSubmoduleEquiv :
    D.descendedAlgebra ≃ₗ[A] D.toDescentDatum.descended :=
  LinearEquiv.ofEq _ _ D.descendedAlgebra_toSubmodule

@[simp]
lemma descendedSubmoduleEquiv_coe (n : D.descendedAlgebra) :
    (D.descendedSubmoduleEquiv n : M) = (n : M) := rfl

/-- The algebra homomorphism `B ⊗[A] descendedAlgebra →ₐ[B] M`, `b ⊗ n ↦ b • n`, induced by the
inclusion `descendedAlgebra ↪ M` and the structure map `B →ₐ[B] M`. -/
noncomputable def descentAlgHom : B ⊗[A] D.descendedAlgebra →ₐ[B] M :=
  Algebra.TensorProduct.lift (Algebra.ofId B M) D.descendedAlgebra.val
    (fun _ _ => Commute.all _ _)

@[simp]
lemma descentAlgHom_tmul (b : B) (n : D.descendedAlgebra) :
    D.descentAlgHom (b ⊗ₜ[A] n) = b • (n : M) := by
  rw [descentAlgHom, Algebra.TensorProduct.lift_tmul]
  exact (Algebra.smul_def b (n : M)).symm

section Flat

variable [Module.Flat A B]

/-- The `A`-linear equivalence `B ⊗[A] descendedAlgebra ≃ₗ[A] B ⊗[A] descended` induced by
`descendedSubmoduleEquiv`. -/
noncomputable def descentTensorCongr :
    B ⊗[A] D.descendedAlgebra ≃ₗ[A] B ⊗[A] D.toDescentDatum.descended :=
  TensorProduct.congr (LinearEquiv.refl A B) D.descendedSubmoduleEquiv

lemma descentAlgHom_toLinearMap :
    D.descentAlgHom.toLinearMap.restrictScalars A =
      D.toDescentDatum.descentEquiv.toLinearMap.restrictScalars A ∘ₗ
        D.descentTensorCongr.toLinearMap := by
  apply TensorProduct.ext'
  intro b n
  simp [descentTensorCongr]

/-- **Theorem F2.b** (effective flat descent of algebras). For `B` flat over `A` and an algebra
descent datum `D` on the `B`-algebra `M`, the map `B ⊗[A] descendedAlgebra → M`, `b ⊗ n ↦ b • n`,
is a `B`-algebra isomorphism. -/
noncomputable def descentAlgEquiv : B ⊗[A] D.descendedAlgebra ≃ₐ[B] M :=
  AlgEquiv.ofBijective D.descentAlgHom (by
    have hbij : Function.Bijective
        (D.toDescentDatum.descentEquiv.toLinearMap.restrictScalars A ∘ₗ
          D.descentTensorCongr.toLinearMap) :=
      (D.toDescentDatum.descentEquiv.bijective).comp D.descentTensorCongr.bijective
    rw [← D.descentAlgHom_toLinearMap] at hbij
    exact hbij)

@[simp]
lemma descentAlgEquiv_tmul (b : B) (n : D.descendedAlgebra) :
    D.descentAlgEquiv (b ⊗ₜ[A] n) = b • (n : M) :=
  D.descentAlgHom_tmul b n

end Flat

section Descent

variable [Module.FaithfullyFlat A B]

/-- Finiteness of `M` over `B` descends to `descendedAlgebra` over `A`. -/
theorem finite_descendedAlgebra [Module.Finite B M] :
    Module.Finite A D.descendedAlgebra := by
  have : Module.Finite B (B ⊗[A] D.descendedAlgebra) :=
    Module.Finite.equiv D.descentAlgEquiv.toLinearEquiv.symm
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat B

/-- Finite type of `M` over `B` descends to `descendedAlgebra` over `A`. -/
theorem finiteType_descendedAlgebra [Algebra.FiniteType B M] :
    Algebra.FiniteType A D.descendedAlgebra := by
  have : Algebra.FiniteType B (B ⊗[A] D.descendedAlgebra) :=
    Algebra.FiniteType.equiv ‹Algebra.FiniteType B M› D.descentAlgEquiv.symm
  exact Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat B

/-- Finite presentation of `M` over `B` descends to `descendedAlgebra` over `A`. -/
theorem finitePresentation_descendedAlgebra [Algebra.FinitePresentation B M] :
    Algebra.FinitePresentation A D.descendedAlgebra := by
  have : Algebra.FinitePresentation B (B ⊗[A] D.descendedAlgebra) :=
    Algebra.FinitePresentation.equiv D.descentAlgEquiv.symm
  exact Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat B

/-- Étaleness of `M` over `B` descends to `descendedAlgebra` over `A`. -/
theorem etale_descendedAlgebra [Algebra.Etale B M] :
    Algebra.Etale A D.descendedAlgebra := by
  have : Algebra.Etale B (B ⊗[A] D.descendedAlgebra) :=
    Algebra.Etale.of_equiv D.descentAlgEquiv.symm
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat B

end Descent

section Canonical

variable (A B)
variable (N : Type*) [CommRing N] [Algebra A N]

/-- The `A`-algebra homomorphism `B ⊗[A] N →ₐ[A] B ⊗[A] (B ⊗[A] N)`, `b ⊗ n ↦ b ⊗ (1 ⊗ n)`,
underlying the canonical algebra descent datum. -/
noncomputable def algCanonicalMap : B ⊗[A] N →ₐ[A] B ⊗[A] (B ⊗[A] N) :=
  Algebra.TensorProduct.map (AlgHom.id A B)
    (Algebra.TensorProduct.includeRight : N →ₐ[A] B ⊗[A] N)

lemma algCanonicalMap_toLinearMap :
    (algCanonicalMap A B N).toLinearMap = (DescentDatum.canonical A B N).τ := by
  apply TensorProduct.ext'
  intro b n
  rfl

lemma algCanonicalMap_apply (x : B ⊗[A] N) :
    algCanonicalMap A B N x = (DescentDatum.canonical A B N).τ x :=
  LinearMap.congr_fun (algCanonicalMap_toLinearMap A B N) x

/-- The canonical algebra descent datum on `B ⊗[A] N` for an `A`-algebra `N`:
`τₐ (b ⊗ n) = b ⊗ (1 ⊗ n)`. -/
noncomputable def canonical : AlgDescentDatum A B (B ⊗[A] N) where
  toDescentDatum := DescentDatum.canonical A B N
  τₐ := algCanonicalMap A B N
  τ_eq := (algCanonicalMap_toLinearMap A B N).symm

@[simp]
lemma canonical_τₐ_tmul (b : B) (n : N) :
    (canonical A B N).τₐ (b ⊗ₜ[A] n) = b ⊗ₜ[A] ((1 : B) ⊗ₜ[A] n) := rfl

/-- `N`, embedded in `B ⊗[A] N` by `n ↦ 1 ⊗ n` (via `Algebra.TensorProduct.includeRight`), lies
in the descended algebra of the canonical datum. -/
theorem includeRight_mem_descendedAlgebra_canonical (n : N) :
    (Algebra.TensorProduct.includeRight : N →ₐ[A] B ⊗[A] N) n ∈
      (canonical A B N).descendedAlgebra := by
  rw [mem_descendedAlgebra_iff]
  rfl

end Canonical

end AlgDescentDatum

end GromovWitten.Algebra
