/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import GromovWitten.AlgebraicGeometry.CotangentComplex.SquareZeroSource

/-! # Independence of the polynomial presentation

Mutual maps of presentations induce inverse maps of obstruction cokernels: their composites
induce the same maps as identities by the homotopy calculation in `SquareZeroSource`.
Polynomial presentations always have comparison maps, obtained by lifting their generators.
Thus the equivalence below requires no supplied isomorphism of cokernels or conormal modules.
-/

namespace GromovWitten.AlgebraicGeometry.CotangentComplex.SquareZero

universe u

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] (M : Ideal B) [Algebra A (B ⧸ M)]
  [IsScalarTower R A (B ⧸ M)] [IsSquareZero M]
  {P P' P'' : Algebra.Extension.{u} R A}

omit [IsScalarTower R A (B ⧸ M)] in
/-- Restriction along the identity presentation map is the identity on obstruction classes. -/
theorem presentationObstructionGroupMap_id :
    presentationObstructionGroupMap M (Algebra.Extension.Hom.id P) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨θ, rfl⟩ := Submodule.Quotient.mk_surjective (coboundary R M P) x
  rw [presentationObstructionGroupMap_mk]
  change Submodule.Quotient.mk (θ.comp (Algebra.Extension.Cotangent.map
    (Algebra.Extension.Hom.id P))) = Submodule.Quotient.mk θ
  rw [Algebra.Extension.Cotangent.map_id, LinearMap.comp_id]

omit [IsScalarTower R A (B ⧸ M)] in
/-- The obstruction cokernel is contravariant in presentation maps. -/
theorem presentationObstructionGroupMap_comp (f : P.Hom P') (g : P'.Hom P'') :
    presentationObstructionGroupMap M (g.comp f) =
      (presentationObstructionGroupMap M f).comp (presentationObstructionGroupMap M g) := by
  apply LinearMap.ext
  intro x
  obtain ⟨θ, rfl⟩ := Submodule.Quotient.mk_surjective (coboundary R M P'') x
  change Submodule.Quotient.mk (θ.comp (Algebra.Extension.Cotangent.map (g.comp f))) =
    Submodule.Quotient.mk ((θ.comp (Algebra.Extension.Cotangent.map g)).comp
      (Algebra.Extension.Cotangent.map f))
  congr 1
  ext x
  simp only [LinearMap.comp_apply, Algebra.Extension.Cotangent.map_comp,
    LinearMap.restrictScalars_apply]

/-- Mutual comparison maps give a linear equivalence of obstruction cokernels. The maps
need not themselves be inverse: their induced cokernel maps are independent of that choice. -/
noncomputable def presentationObstructionEquiv (f : P.Hom P') (g : P'.Hom P) :
    ObstructionGroup R M P' ≃ₗ[A] ObstructionGroup R M P :=
  LinearEquiv.ofLinearMap (presentationObstructionGroupMap M f)
    (presentationObstructionGroupMap M g)
    (by
      rw [← presentationObstructionGroupMap_comp,
        presentationObstructionGroupMap_eq M (g.comp f) (Algebra.Extension.Hom.id P),
        presentationObstructionGroupMap_id])
    (by
      rw [← presentationObstructionGroupMap_comp,
        presentationObstructionGroupMap_eq M (f.comp g) (Algebra.Extension.Hom.id P'),
        presentationObstructionGroupMap_id])

/-- The canonical obstruction equivalence between any two polynomial presentations.
Comparison maps are constructed using the chosen lifts of polynomial generators. -/
noncomputable def generatorsObstructionEquiv {ι κ : Type u}
    (G : Algebra.Generators R A ι) (H : Algebra.Generators R A κ) :
    ObstructionGroup R M H.toExtension ≃ₗ[A] ObstructionGroup R M G.toExtension :=
  presentationObstructionEquiv M (Algebra.Generators.defaultHom G H).toExtensionHom
    (Algebra.Generators.defaultHom H G).toExtensionHom

attribute [local instance] ringAlgebra isScalarTower_ring isScalarTower_base

/-- The presentation equivalence carries the actual obstruction class to the same lifting
problem computed in the other presentation. -/
theorem presentationObstructionEquiv_obstruction (f : P.Hom P') (g : P'.Hom P)
    [Nonempty (Lift R M P.Ring)] [Nonempty (Lift R M P'.Ring)] :
    presentationObstructionEquiv M f g (obstruction R M P') = obstruction R M P :=
  presentationObstructionGroupMap_obstruction M f

/-- Polynomial presentations compute the same actual obstruction, without an ambient-lift
hypothesis: polynomial algebras are formally smooth. -/
theorem generatorsObstructionEquiv_obstruction {ι κ : Type u}
    (G : Algebra.Generators R A ι) (H : Algebra.Generators R A κ) :
    generatorsObstructionEquiv M G H (obstruction R M H.toExtension) =
      obstruction R M G.toExtension :=
  presentationObstructionEquiv_obstruction M
    (Algebra.Generators.defaultHom G H).toExtensionHom
    (Algebra.Generators.defaultHom H G).toExtensionHom

end GromovWitten.AlgebraicGeometry.CotangentComplex.SquareZero
