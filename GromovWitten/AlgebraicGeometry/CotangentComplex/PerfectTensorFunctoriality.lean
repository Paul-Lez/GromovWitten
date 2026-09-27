/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/

import GromovWitten.AlgebraicGeometry.CotangentComplex.PerfectTensor

/-!
# Functoriality of the derived tensor product of perfect complexes

This file continues `CotangentComplex/PerfectTensor.lean`.  It upgrades the termwise object
isomorphism `PerfectTensor.tensorSingleXIso` to an isomorphism of *complexes* `K ⊗ M[0] ≅
PerfectComplex.tensorRight K M`, and constructs functoriality maps for `derivedTensor` in each
variable.

## Main definitions

* `singleZero`, `tensorSingleXIso_inv_comm`, `singleZeroIso` : the chain-level comparison
  `K ⊗ M[0] ≅ tensorRight K M` (`tensorSingleXIso` itself is `PerfectTensor.tensorSingleXIso`).
* `derivedTensor_single_iso` : the derived tensor product of a perfect object with `M[0]`
  (`M` finite free) is `Q.obj (tensorRight (representative) M)`.
* `Q_map_tensorHom_right_congr`, `Q_map_tensorHom_left_congr` : independence of the chain-map
  realisation of a derived morphism, after tensoring with a fixed strictly perfect complex.
* `derivedTensorMap`, `derivedTensorMap_id`, `derivedTensorMap_comp` : functoriality of
  `derivedTensor` in the first variable.
* `derivedTensorMapLeft`, `derivedTensorMapLeft_id`, `derivedTensorMapLeft_comp` :
  functoriality of `derivedTensor` in the second variable.

## What is not proved

The braiding `derivedTensor E F ≅ derivedTensor F E` is not constructed.  Mathlib does *not*
equip `HomologicalComplex C c` with a braided/symmetric monoidal structure: it has a braiding
`GradedObject.Monoidal.braiding` for the underlying *graded objects* (no Koszul sign, since a
graded object carries no differential), but no version compatible with differentials (no file
anywhere in Mathlib combines `HomologicalComplex` with `Braided`/`SymmetricCategory`/
`braiding`).  Building the Koszul-signed swap `K ⊗ L ≅ L ⊗ K` (sign `(-1)^{ij}` on the
`K.X i ⊗ L.X j` summand) and checking its differential compatibility directly is a two-sided
version of the one-sided check done for `tensorSingleXIso_inv_comm` above (there, one of the two
`d₁`/`d₂` contributions vanished identically because `M[0]` has a single nonzero degree; here
both are live and interact through the sign rule `ε₂ (p, q) = c.ε p`), assessed as substantially
more work than the remaining time allows to do safely; see the repository issue tracker (`#55`)
for this follow-up.
-/

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

namespace GromovWitten.AlgebraicGeometry.CotangentComplex

namespace PerfectComplex

universe u

variable {R : Type u} [CommRing R]

/-! ## Comparison with `tensorRight` -/

section TensorRightComparison

variable (K : CochainComplex (ModuleCat.{u} R) ℤ) (M : ModuleCat.{u} R)

/-- The module `M` placed in cohomological degree `0`, as a single complex. -/
noncomputable abbrev singleZero : CochainComplex (ModuleCat.{u} R) ℤ :=
  (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj M

/-- Tensoring `K` with `M[0]` kills the second-factor contribution to the differential of the
tensor product of complexes: the generalisation, to an arbitrary module `M` in place of the
monoidal unit, of Mathlib's `HomologicalComplex.tensor_unit_d₂`. -/
theorem singleZero_d₂ (i₁ i₂ j : ℤ) :
    HomologicalComplex.mapBifunctor.d₂ K (singleZero M)
        (MonoidalCategory.curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ) i₁ i₂ j = 0 := by
  by_cases h₁ : (ComplexShape.up ℤ).Rel i₂ ((ComplexShape.up ℤ).next i₂)
  · by_cases h₂ : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (i₁, (ComplexShape.up ℤ).next i₂) = j
    · rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _ h₁ _ h₂,
        HomologicalComplex.single_obj_d, Functor.map_zero, zero_comp, smul_zero]
    · rw [HomologicalComplex.mapBifunctor.d₂_eq_zero' _ _ _ _ _ h₁ _ h₂]
  · rw [HomologicalComplex.mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ h₁]

/-- The explicit value of `(tensorSingleXIso K M n).inv`: definitional (`tensorSingleXIso` is
`PerfectTensor.tensorSingleXIso`), recorded as a named `rfl`-lemma so later proofs can rewrite
with it instead of unfolding `tensorSingleXIso`. -/
theorem tensorSingleXIso_inv (n : ℤ) :
    (tensorSingleXIso K M n).inv =
      (𝟙 (K.X n) ⊗ₘ (HomologicalComplex.singleObjXSelf _ 0 M).inv) ≫
        HomologicalComplex.ιTensorObj K (singleZero M) n 0 n (by ring) :=
  rfl

/-- `tensorRight K M`'s differential is the plain whiskering `K.d i j ▷ M`: there is no Koszul
sign, matching `TotalComplexShape c c c`'s `ε₁ = 1`. -/
theorem tensorRight_d (i j : ℤ) : (PerfectComplex.tensorRight K M).d i j = (K.d i j) ▷ M := rfl

/-- **Differential compatibility of `tensorSingleXIso`.**  The termwise isomorphism intertwines
the differential of `K ⊗ M[0]` with that of `PerfectComplex.tensorRight K M`.  Stated with
`HomologicalComplex.tensorObj` (rather than the `⊗` notation coming from the `MonoidalCategory`
instance) so that `simp`/`rw` can see through it to the `mapBifunctor` API: the `MonoidalCategory`
instance on `HomologicalComplex` is registered via `Monoidal.induced`, which is opaque to the
simplifier even though it is *defeq* to `HomologicalComplex.tensorObj`. -/
theorem tensorSingleXIso_inv_comm (i j : ℤ) :
    (tensorSingleXIso K M i).inv ≫ (HomologicalComplex.tensorObj K (singleZero M)).d i j =
      (PerfectComplex.tensorRight K M).d i j ≫ (tensorSingleXIso K M j).inv := by
  by_cases hij : (ComplexShape.up ℤ).Rel i j
  · simp only [tensorSingleXIso_inv, Category.assoc, HomologicalComplex.mapBifunctor.d_eq,
      Preadditive.comp_add, HomologicalComplex.mapBifunctor.ι_D₁,
      HomologicalComplex.mapBifunctor.ι_D₂, singleZero_d₂, comp_zero, add_zero]
    rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ hij 0 j (by simp)]
    have hε : ((ComplexShape.up ℤ).ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (i, (0 : ℤ))) =
        1 := rfl
    have hmap : ((MonoidalCategory.curriedTensor (ModuleCat.{u} R)).map (K.d i j)).app
        ((singleZero M).X 0) = (K.d i j) ▷ ((singleZero M).X 0) := rfl
    rw [hε, one_smul, hmap, tensorRight_d, MonoidalCategory.id_tensorHom,
      MonoidalCategory.id_tensorHom, MonoidalCategory.whisker_exchange_assoc]
    rfl
  · have e1 : (tensorSingleXIso K M i).inv ≫ (HomologicalComplex.tensorObj K (singleZero M)).d i j
        = 0 := by
      rw [HomologicalComplex.shape _ i j hij]
      exact comp_zero
    have e2 : (PerfectComplex.tensorRight K M).d i j ≫ (tensorSingleXIso K M j).inv = 0 := by
      rw [HomologicalComplex.shape _ i j hij]
      exact zero_comp
    exact e1.trans e2.symm

/-- **Chain-level comparison with `tensorRight`.**  Tensoring `K` with `M` placed in degree `0`
agrees, as a complex, with `PerfectComplex.tensorRight K M` (tensoring termwise with `M`). -/
noncomputable def singleZeroIso :
    HomologicalComplex.tensorObj K (singleZero M) ≅ PerfectComplex.tensorRight K M :=
  (HomologicalComplex.Hom.isoOfComponents (fun n => (tensorSingleXIso K M n).symm)
    (fun i j _ => tensorSingleXIso_inv_comm K M i j)).symm

end TensorRightComparison

section DerivedSingle

attribute [local instance] HasDerivedCategory.standard

/-- **The derived tensor product of a perfect object with `M[0]`** (`M` finite free) is
`Q.obj (tensorRight (rep) M)`. -/
noncomputable def derivedTensor_single_iso {E : DerivedCategory (ModuleCat.{u} R)}
    (hE : IsPerfect E) {M : ModuleCat.{u} R} (hM : IsFiniteFree M)
    (hF : IsPerfect (DerivedCategory.Q.obj (singleZero M))) :
    derivedTensor hE hF ≅ DerivedCategory.Q.obj (PerfectComplex.tensorRight hE.rep M) :=
  tensorIsoLeft hE.rep hF.rep_isStrictlyPerfect (isStrictlyPerfect_single hM 0) hF.repIso ≪≫
    DerivedCategory.Q.mapIso (singleZeroIso hE.rep M)

end DerivedSingle

/-! ## Functoriality of `derivedTensor` in each variable -/

section Functoriality

attribute [local instance] HasDerivedCategory.standard

/-- **Independence of the chain-map realisation, tensoring on the right.**  Two chain maps out
of a strictly perfect complex with the same image in the derived category still have the same
image after tensoring with the identity of a fixed complex `N`. -/
theorem Q_map_tensorHom_right_congr {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyPerfect K) {φ ψ : K ⟶ L}
    (h : DerivedCategory.Q.map φ = DerivedCategory.Q.map ψ)
    (N : CochainComplex (ModuleCat.{u} R) ℤ) :
    DerivedCategory.Q.map (φ ⊗ₘ 𝟙 N) = DerivedCategory.Q.map (ψ ⊗ₘ 𝟙 N) := by
  have _ := hK.isKProjective
  have key : ∀ χ : K ⟶ L,
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map χ) =
        (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.app K ≫
          DerivedCategory.Q.map χ ≫
          (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).inv.app L := by
    intro χ
    have hnat := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.naturality χ
    rw [Functor.comp_map] at hnat
    rw [← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  have hq : (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map φ =
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map ψ := by
    refine (CochainComplex.IsKProjective.Qh_map_bijective K
      ((HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj L)).injective ?_
    rw [key φ, key ψ, h]
  exact DerivedCategory.Q_map_eq_of_homotopy _
    (homotopyTensorHomRight (HomotopyCategory.homotopyOfEq _ _ hq))

/-- **Independence of the chain-map realisation, tensoring on the left.**  Two chain maps out of
a strictly perfect complex with the same image in the derived category still have the same
image after tensoring the identity of a fixed complex `K` with them. -/
theorem Q_map_tensorHom_left_congr {L L' : CochainComplex (ModuleCat.{u} R) ℤ}
    (hL : IsStrictlyPerfect L) {ψ ψ' : L ⟶ L'}
    (h : DerivedCategory.Q.map ψ = DerivedCategory.Q.map ψ')
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    DerivedCategory.Q.map (𝟙 K ⊗ₘ ψ) = DerivedCategory.Q.map (𝟙 K ⊗ₘ ψ') := by
  have _ := hL.isKProjective
  have key : ∀ χ : L ⟶ L',
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map χ) =
        (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.app L ≫
          DerivedCategory.Q.map χ ≫
          (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).inv.app L' := by
    intro χ
    have hnat := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.naturality χ
    rw [Functor.comp_map] at hnat
    rw [← Category.assoc, ← hnat, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  have hq : (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map ψ =
      (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map ψ' := by
    refine (CochainComplex.IsKProjective.Qh_map_bijective L
      ((HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj L')).injective ?_
    rw [key ψ, key ψ', h]
  exact DerivedCategory.Q_map_eq_of_homotopy _
    (homotopyTensorHomLeft (HomotopyCategory.homotopyOfEq _ _ hq))

variable {E E' E'' F F' F'' : DerivedCategory (ModuleCat.{u} R)}

/-- **Functoriality of `derivedTensor` in the first variable.**  A morphism `u : E ⟶ E'` between
perfect objects induces a morphism between their derived tensor products with a fixed perfect
`F`, realising `u` as a chain map between the chosen strictly perfect representatives (via
`PerfectDualInvariance.derivedChainMap`) and tensoring with the identity on `hF.rep`. -/
noncomputable def derivedTensorMap (hE : IsPerfect E) (hE' : IsPerfect E') (hF : IsPerfect F)
    (u : E ⟶ E') : derivedTensor hE hF ⟶ derivedTensor hE' hF :=
  DerivedCategory.Q.map
    (derivedChainMap hE.rep_isStrictlyPerfect (hE.repIso.hom ≫ u ≫ hE'.repIso.inv) ⊗ₘ 𝟙 hF.rep)

/-- `derivedTensorMap` sends the identity to the identity. -/
theorem derivedTensorMap_id (hE : IsPerfect E) (hF : IsPerfect F) :
    derivedTensorMap hE hE hF (𝟙 E) = 𝟙 (derivedTensor hE hF) := by
  have h : DerivedCategory.Q.map
      (derivedChainMap hE.rep_isStrictlyPerfect (hE.repIso.hom ≫ 𝟙 E ≫ hE.repIso.inv)) =
      DerivedCategory.Q.map (𝟙 hE.rep) := by
    rw [Q_map_derivedChainMap, Category.id_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  unfold derivedTensorMap
  rw [Q_map_tensorHom_right_congr hE.rep_isStrictlyPerfect h hF.rep,
    MonoidalCategory.id_tensorHom_id, CategoryTheory.Functor.map_id]
  rfl

/-- `derivedTensorMap` is compatible with composition. -/
theorem derivedTensorMap_comp (hE : IsPerfect E) (hE' : IsPerfect E') (hE'' : IsPerfect E'')
    (hF : IsPerfect F) (u : E ⟶ E') (v : E' ⟶ E'') :
    derivedTensorMap hE hE'' hF (u ≫ v) =
      derivedTensorMap hE hE' hF u ≫ derivedTensorMap hE' hE'' hF v := by
  have h : DerivedCategory.Q.map
      (derivedChainMap hE.rep_isStrictlyPerfect (hE.repIso.hom ≫ (u ≫ v) ≫ hE''.repIso.inv)) =
      DerivedCategory.Q.map
        (derivedChainMap hE.rep_isStrictlyPerfect (hE.repIso.hom ≫ u ≫ hE'.repIso.inv) ≫
          derivedChainMap hE'.rep_isStrictlyPerfect (hE'.repIso.hom ≫ v ≫ hE''.repIso.inv)) := by
    rw [CategoryTheory.Functor.map_comp, Q_map_derivedChainMap, Q_map_derivedChainMap,
      Q_map_derivedChainMap]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  unfold derivedTensorMap
  rw [Q_map_tensorHom_right_congr hE.rep_isStrictlyPerfect h hF.rep,
    MonoidalCategory.comp_tensor_id, CategoryTheory.Functor.map_comp]
  rfl

/-- **Functoriality of `derivedTensor` in the second variable.**  A morphism `v : F ⟶ F'`
between perfect objects induces a morphism between the derived tensor products of a fixed
perfect `E` with them. -/
noncomputable def derivedTensorMapLeft (hE : IsPerfect E) (hF : IsPerfect F) (hF' : IsPerfect F')
    (v : F ⟶ F') : derivedTensor hE hF ⟶ derivedTensor hE hF' :=
  DerivedCategory.Q.map
    (𝟙 hE.rep ⊗ₘ derivedChainMap hF.rep_isStrictlyPerfect (hF.repIso.hom ≫ v ≫ hF'.repIso.inv))

/-- `derivedTensorMapLeft` sends the identity to the identity. -/
theorem derivedTensorMapLeft_id (hE : IsPerfect E) (hF : IsPerfect F) :
    derivedTensorMapLeft hE hF hF (𝟙 F) = 𝟙 (derivedTensor hE hF) := by
  have h : DerivedCategory.Q.map
      (derivedChainMap hF.rep_isStrictlyPerfect (hF.repIso.hom ≫ 𝟙 F ≫ hF.repIso.inv)) =
      DerivedCategory.Q.map (𝟙 hF.rep) := by
    rw [Q_map_derivedChainMap, Category.id_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  unfold derivedTensorMapLeft
  rw [Q_map_tensorHom_left_congr hF.rep_isStrictlyPerfect h hE.rep,
    MonoidalCategory.id_tensorHom_id, CategoryTheory.Functor.map_id]
  rfl

/-- `derivedTensorMapLeft` is compatible with composition. -/
theorem derivedTensorMapLeft_comp (hE : IsPerfect E) (hF : IsPerfect F) (hF' : IsPerfect F')
    (hF'' : IsPerfect F'') (v : F ⟶ F') (w : F' ⟶ F'') :
    derivedTensorMapLeft hE hF hF'' (v ≫ w) =
      derivedTensorMapLeft hE hF hF' v ≫ derivedTensorMapLeft hE hF' hF'' w := by
  have h : DerivedCategory.Q.map
      (derivedChainMap hF.rep_isStrictlyPerfect (hF.repIso.hom ≫ (v ≫ w) ≫ hF''.repIso.inv)) =
      DerivedCategory.Q.map
        (derivedChainMap hF.rep_isStrictlyPerfect (hF.repIso.hom ≫ v ≫ hF'.repIso.inv) ≫
          derivedChainMap hF'.rep_isStrictlyPerfect (hF'.repIso.hom ≫ w ≫ hF''.repIso.inv)) := by
    rw [CategoryTheory.Functor.map_comp, Q_map_derivedChainMap, Q_map_derivedChainMap,
      Q_map_derivedChainMap]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  unfold derivedTensorMapLeft
  rw [Q_map_tensorHom_left_congr hF.rep_isStrictlyPerfect h hE.rep,
    MonoidalCategory.id_tensor_comp, CategoryTheory.Functor.map_comp]
  rfl

end Functoriality

end PerfectComplex

end GromovWitten.AlgebraicGeometry.CotangentComplex
