/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.TotalNormalizationNormal
import GromovWitten.AlgebraicGeometry.Curves.NormalizationSigma

/-!
# Irreducible neighbourhoods from normalization

When total normalization is an isomorphism, its finite coproduct decomposition gives an
open cover by integral schemes. In particular, an étale scheme over affine space has
irreducible open neighbourhoods, and a point in an irreducible open subset belongs to a
unique irreducible component.
-/

open CategoryTheory Limits AlgebraicGeometry Topology
namespace GromovWitten.AlgebraicGeometry.Curves
universe u

lemma components_eq_of_irreducible_open {X : Scheme.{u}} {x : X} {U : Set X}
    (hU : IsOpen U) (hUI : IsIrreducible U) (hx : x ∈ U)
    {C D : Component X} (hxC : x ∈ (C : Set X)) (hxD : x ∈ (D : Set X)) : C = D := by
  obtain ⟨E, hE, hUE⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible U hUI
  have heq (A : Component X) (hxA : x ∈ (A : Set X)) : (A : Set X) = E := by
    apply A.property.eq_of_le hE.1
    exact (subset_closure_inter_of_isPreirreducible_of_isOpen A.property.1.2 hU
      ⟨x, hxA, hx⟩).trans
        (closure_minimal (fun _ hz ↦ hUE hz.2)
          (isClosed_of_mem_irreducibleComponents E hE))
  exact Subtype.ext ((heq C hxC).trans (heq D hxD).symm)

lemma components_eq_of_irreducible_open_map {X Y : Scheme.{u}} [IrreducibleSpace Y]
    (f : Y ⟶ X) (hf : IsOpenMap f) (y : Y)
    {C D : Component X} (hyC : f y ∈ (C : Set X)) (hyD : f y ∈ (D : Set X)) : C = D := by
  apply components_eq_of_irreducible_open hf.isOpen_range
    (by simpa using ((IrreducibleSpace.isIrreducible_univ Y).image f f.continuous.continuousOn))
    (Set.mem_range_self y) hyC hyD

end GromovWitten.AlgebraicGeometry.Curves

namespace GromovWitten.AlgebraicGeometry.Curves
universe u
noncomputable section
variable {X : Scheme.{u}} [IsNoetherian X] [IsIso (totalNormalizationToScheme X)]

lemma exists_integral_openImmersion_of_totalNormalization_isIso (x : X) :
    ∃ (Y : Scheme.{u}) (j : Y ⟶ X), IsIntegral Y ∧ IsOpenImmersion j ∧
      ∃ y : Y, j y = x := by
  let _ : Fintype (GenericPointSet X) := Fintype.ofFinite _
  let S := genericPointSpectrum X
  let f := genericPointsToScheme X
  let _ (i : GenericPointSet X) : QuasiCompact (Sigma.ι S i ≫ f) := inferInstance
  let _ (i : GenericPointSet X) : QuasiSeparated (Sigma.ι S i ≫ f) := inferInstance
  let N (i : GenericPointSet X) := (Sigma.ι S i ≫ f).normalization
  let e : (∐ N) ≅ totalNormalization X := Scheme.Hom.normalizationSigmaIso f
  let g : (∐ N) ⟶ X := e.hom ≫ totalNormalizationToScheme X
  let _ : IsIso g := inferInstance
  obtain ⟨p, hp⟩ := Scheme.Hom.surjective g x
  obtain ⟨⟨i, y⟩, rfl⟩ := (sigmaMk N).surjective p
  refine ⟨N i, Sigma.ι N i ≫ g, ?_, inferInstance, y, ?_⟩
  · dsimp [N, S]
    infer_instance
  · simpa only [sigmaMk_mk, Scheme.Hom.comp_apply] using hp

lemma components_eq_of_totalNormalization_isIso {x : X}
    {C D : Component X} (hxC : x ∈ (C : Set X)) (hxD : x ∈ (D : Set X)) : C = D := by
  obtain ⟨Y, j, hY, hj, y, rfl⟩ :=
    exists_integral_openImmersion_of_totalNormalization_isIso x
  let _ := hY
  let _ := hj
  exact components_eq_of_irreducible_open_map j j.isOpenEmbedding.isOpenMap y hxC hxD

end
end GromovWitten.AlgebraicGeometry.Curves

namespace GromovWitten.AlgebraicGeometry.Curves
universe u
noncomputable section
lemma exists_integral_openImmersion_of_etale_affineSpace
    {Y : Scheme.{u}} [IsNoetherian Y] (R : Type u) [Field R] (n : ℕ)
    (g : Y ⟶ Spec (.of (MvPolynomial (Fin n) R))) [Etale g] (y : Y) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ Y), IsIntegral Z ∧ IsOpenImmersion j ∧
      ∃ z : Z, j z = y := by
  let P := Spec (.of (MvPolynomial (Fin n) R))
  let _ : IsIso (totalNormalizationToScheme P) :=
    totalNormalizationToScheme_isIso_of_normal P (spec_isNormalScheme _)
  let _ : IsIso (totalNormalizationToScheme Y) :=
    totalNormalizationToScheme_isIso_of_etale g
  exact exists_integral_openImmersion_of_totalNormalization_isIso y
end
end GromovWitten.AlgebraicGeometry.Curves
