/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.Algebra.TensorKernel
import GromovWitten.CategoryTheory.HomologyBaseChange
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Homology and arbitrary scalar extension

The canonical kernel comparison for scalar extension is identified with `LinearMap.tensorKer`.
If the target and cokernel of a differential are flat over the original ring, this comparison
is invertible for every new algebra. Consequently the canonical homology comparison is also
invertible. Neither the source module nor the new algebra is required to be flat.
-/

open CategoryTheory Limits
noncomputable section
universe u
namespace ModuleCat
variable {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A) {M N : ModuleCat.{u} R} (f : M ⟶ N)

set_option backward.isDefEq.respectTransparency false in
/-- Scalar extension preserves this kernel when the target and cokernel are flat. -/
lemma preservesKernel_extendScalars_of_flat_cokernel
    [Module.Flat R N] [Module.Flat R ((cokernel f : ModuleCat R) : Type u)] :
    PreservesLimit (parallelPair f 0) (extendScalars φ) := by
  let _ : Algebra R A := φ.toAlgebra
  let F := extendScalars φ
  have : Module.Flat R (N ⧸ LinearMap.range f.hom) :=
    Module.Flat.of_linearEquiv (cokernelIsoRangeQuotient f).toLinearEquiv.symm
  let k : F.obj (ModuleCat.of R (LinearMap.ker f.hom)) ⟶
      ModuleCat.of A (LinearMap.ker (F.map f).hom) :=
    ModuleCat.ofHom (LinearMap.tensorKer A A f.hom)
  have hk : IsIso k := (ConcreteCategory.isIso_iff_bijective k).mpr
    (LinearMap.tensorKer_bijective_of_target_flat_of_cokernel_flat f.hom)
  have hi : k ≫ ModuleCat.ofHom (LinearMap.ker (F.map f).hom).subtype =
      F.map (ModuleCat.ofHom (LinearMap.ker f.hom).subtype) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact LinearMap.tensorKer_coe A A f.hom x
  have he : kernelComparison f F =
      F.map (kernelIsoKer f).hom ≫ k ≫ (kernelIsoKer (F.map f)).inv := by
    apply (cancel_mono (kernel.ι (F.map f))).mp
    rw [kernelComparison_comp_ι, Category.assoc, Category.assoc,
      kernelIsoKer_inv_kernel_ι, hi, ← F.map_comp, kernelIsoKer_hom_ker_subtype]
  have : IsIso (kernelComparison f F) := by rw [he]; infer_instance
  exact PreservesKernel.of_iso_comparison F f

end ModuleCat

namespace CategoryTheory.ShortComplex
variable {R A : Type u} [CommRing R] [CommRing A]
    (S : ShortComplex (ModuleCat.{u} R)) (φ : R →+* A)

/-- Homology commutes with arbitrary scalar extension if the outgoing differential has flat
target and flat cokernel. -/
lemma isIso_homologyComparison_extendScalars_of_flat_cokernel
    [Module.Flat R S.X₃]
    [Module.Flat R ((cokernel S.g : ModuleCat R) : Type u)] :
    IsIso (S.homologyComparison (ModuleCat.extendScalars φ)) := by
  have := ModuleCat.preservesKernel_extendScalars_of_flat_cokernel φ S.g
  exact S.isIso_homologyComparison_of_preservesKernel (ModuleCat.extendScalars φ)

end CategoryTheory.ShortComplex

namespace HomologicalComplex
variable {R A : Type u} [CommRing R] [CommRing A] {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{u} R) c) (i : ι) (φ : R →+* A)

/-- Homology commutes with arbitrary scalar extension if the outgoing differential has flat
target and flat cokernel. -/
lemma isIso_homologyComparison_extendScalars_of_flat_cokernel
    [Module.Flat R (K.X (c.next i))]
    [Module.Flat R ((cokernel (K.d i (c.next i)) : ModuleCat R) : Type u)] :
    IsIso (K.homologyComparison (ModuleCat.extendScalars φ) i) := by
  have : Module.Flat R (K.sc i).X₃ :=
    inferInstanceAs (Module.Flat R (K.X (c.next i)))
  have : Module.Flat R ((cokernel (K.sc i).g : ModuleCat R) : Type u) :=
    inferInstanceAs (Module.Flat R ((cokernel (K.d i (c.next i)) : ModuleCat R) : Type u))
  exact (K.sc i).isIso_homologyComparison_extendScalars_of_flat_cokernel φ

end HomologicalComplex
