/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Modules.Stack
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Coherence maps for the sheafified module tensor

The tensor in `Modules.Stack` is the sheafification of the pointwise presheaf tensor.  The
comparison below is the canonical map induced by the sheafification unit. Its invertibility is
proved for every finite free sheaf factor, using finite coproducts of the unit. This constructs
an associator when the two outer factors have global finite free trivialisations, with arbitrary
middle factor. Symmetry is natural and involutive for arbitrary module sheaves. The comparison
for arbitrary sheaf factors is kept as a morphism because its
invertibility requires the missing local tensor-preservation theorem. General associativity and
the full coherence laws remain open.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.BraidedCategory

namespace GromovWitten.AlgebraicGeometry.Modules

universe w v u

variable {C : Type u} [Category.{v} C]
  [UnivLE.{max u v, w}]
  (S : Sites.RingedSite.{w} C)
  [∀ X, HasWeakSheafify (S.topology.over X) AddCommGrpCat.{w}]
  [∀ X, (S.topology.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]

section TensorCoherence

variable [HasWeakSheafify S.topology AddCommGrpCat.{w}]
  [S.topology.WEqualsLocallyBijective AddCommGrpCat.{w}]

noncomputable def moduleSheafification :
    PresheafOfModules S.ringStructureSheaf.obj ⥤ S.Modules :=
  PresheafOfModules.sheafification
    (R₀ := S.ringStructureSheaf.obj) (R := S.ringStructureSheaf)
      (𝟙 S.ringStructureSheaf.obj)

noncomputable def modulePresheafTensor
    (P Q : PresheafOfModules S.ringStructureSheaf.obj) :
    PresheafOfModules S.ringStructureSheaf.obj :=
  PresheafOfModules.Monoidal.tensorObj (R := S.structureSheaf.obj) P Q

/-! The existing bifunctor is left adjoint in each presheaf variable after forgetting module
structures.  We expose its currying here so finite free factors can be handled through the
colimit presentation of `SheafOfModules.free`. -/

noncomputable def tensorRightFunctor (M : S.Modules) : S.Modules ⥤ S.Modules :=
  (Functor.curryObj (tensor S)).obj M

noncomputable def tensorLeftFunctor (N : S.Modules) : S.Modules ⥤ S.Modules :=
  ((Functor.curryObj (tensor S)).flip).obj N

noncomputable def tensorRightUnderlyingFunctor (M : S.Modules) : S.Modules ⥤ S.Modules :=
  by
    letI : Presheaf.IsLocallyInjective S.topology
        (𝟙 S.ringStructureSheaf.obj) := inferInstance
    letI : Presheaf.IsLocallySurjective S.topology
        (𝟙 S.ringStructureSheaf.obj) := inferInstance
    letI : MonoidalCategory (PresheafOfModules S.ringStructureSheaf.obj) :=
      PresheafOfModules.monoidalCategory (R := S.structureSheaf.obj)
    exact (SheafOfModules.forget S.ringStructureSheaf) ⋙
      MonoidalCategory.tensorLeft
        (C := PresheafOfModules
          (S.structureSheaf.obj ⋙ forget₂ CommRingCat RingCat))
        (show PresheafOfModules
          (S.structureSheaf.obj ⋙ forget₂ CommRingCat RingCat) from M.val) ⋙
        moduleSheafification S

omit [∀ X, HasWeakSheafify (S.topology.over X) AddCommGrpCat.{w}]
  [∀ X, (S.topology.over X).WEqualsLocallyBijective AddCommGrpCat.{w}] in
theorem tensorRightFunctor_eq_underlying (M : S.Modules) :
    tensorRightFunctor S M = tensorRightUnderlyingFunctor S M := by
  rfl

noncomputable def tensorSheafificationRightFunctor
    (P : PresheafOfModules S.ringStructureSheaf.obj) : S.Modules ⥤ S.Modules := by
  letI : Presheaf.IsLocallyInjective S.topology
      (𝟙 S.ringStructureSheaf.obj) := inferInstance
  letI : Presheaf.IsLocallySurjective S.topology
      (𝟙 S.ringStructureSheaf.obj) := inferInstance
  letI : MonoidalCategory (PresheafOfModules S.ringStructureSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := S.structureSheaf.obj)
  exact (SheafOfModules.forget S.ringStructureSheaf) ⋙
    MonoidalCategory.tensorLeft
      (C := PresheafOfModules
        (S.structureSheaf.obj ⋙ forget₂ CommRingCat RingCat))
      (show PresheafOfModules
        (S.structureSheaf.obj ⋙ forget₂ CommRingCat RingCat) from P) ⋙
      moduleSheafification S

set_option linter.style.haveILetI false in
omit [∀ X, HasWeakSheafify (S.topology.over X) AddCommGrpCat.{w}]
  [∀ X, (S.topology.over X).WEqualsLocallyBijective AddCommGrpCat.{w}] in
theorem tensorSheafificationRightFunctor_preservesFiniteCoproducts
    (P : PresheafOfModules S.ringStructureSheaf.obj) :
    PreservesFiniteCoproducts (tensorSheafificationRightFunctor S P) := by
  letI : Presheaf.IsLocallyInjective S.topology
      (𝟙 S.ringStructureSheaf.obj) := inferInstance
  letI : Presheaf.IsLocallySurjective S.topology
      (𝟙 S.ringStructureSheaf.obj) := inferInstance
  letI : MonoidalCategory (PresheafOfModules S.ringStructureSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := S.structureSheaf.obj)
  haveI : PreservesFiniteCoproducts (SheafOfModules.forget S.ringStructureSheaf) := by
    infer_instance
  haveI : PreservesFiniteCoproducts
      (MonoidalCategory.tensorLeft
        (C := PresheafOfModules
          (S.structureSheaf.obj ⋙ forget₂ CommRingCat RingCat))
        (show PresheafOfModules
          (S.structureSheaf.obj ⋙ forget₂ CommRingCat RingCat) from P)) := by
    letI : PreservesColimitsOfSize.{w, w}
        (MonoidalCategory.tensorLeft
          (C := PresheafOfModules
            (S.structureSheaf.obj ⋙ forget₂ CommRingCat RingCat))
          (show PresheafOfModules
            (S.structureSheaf.obj ⋙ forget₂ CommRingCat RingCat) from P)) := by
      infer_instance
    letI : PreservesFiniteColimits
        (MonoidalCategory.tensorLeft
          (C := PresheafOfModules
            (S.structureSheaf.obj ⋙ forget₂ CommRingCat RingCat))
          (show PresheafOfModules
            (S.structureSheaf.obj ⋙ forget₂ CommRingCat RingCat) from P)) :=
      PreservesColimitsOfSize.preservesFiniteColimits _
    exact ⟨fun n => inferInstance⟩
  haveI : PreservesFiniteCoproducts
      (PresheafOfModules.sheafification
        (R₀ := S.ringStructureSheaf.obj) (R := S.ringStructureSheaf)
          (𝟙 S.ringStructureSheaf.obj)) := by
    letI : (PresheafOfModules.sheafification
      (R₀ := S.ringStructureSheaf.obj) (R := S.ringStructureSheaf)
        (𝟙 S.ringStructureSheaf.obj)).IsLeftAdjoint := inferInstance
    letI : PreservesColimitsOfSize.{w, w}
        (PresheafOfModules.sheafification
          (R₀ := S.ringStructureSheaf.obj) (R := S.ringStructureSheaf)
            (𝟙 S.ringStructureSheaf.obj)) := by
      infer_instance
    letI : PreservesFiniteColimits
        (PresheafOfModules.sheafification
          (R₀ := S.ringStructureSheaf.obj) (R := S.ringStructureSheaf)
            (𝟙 S.ringStructureSheaf.obj)) :=
      PreservesColimitsOfSize.preservesFiniteColimits _
    refine ⟨fun n => ?_⟩
    infer_instance
  let U : S.Modules ⥤ PresheafOfModules S.ringStructureSheaf.obj :=
    SheafOfModules.forget S.ringStructureSheaf
  let T : PresheafOfModules S.ringStructureSheaf.obj ⥤
      PresheafOfModules S.ringStructureSheaf.obj :=
    MonoidalCategory.tensorLeft
      (C := PresheafOfModules
        (S.structureSheaf.obj ⋙ forget₂ CommRingCat RingCat))
      (show PresheafOfModules
        (S.structureSheaf.obj ⋙ forget₂ CommRingCat RingCat) from P)
  let H : PresheafOfModules S.ringStructureSheaf.obj ⥤ S.Modules :=
    PresheafOfModules.sheafification
      (R₀ := S.ringStructureSheaf.obj) (R := S.ringStructureSheaf)
        (𝟙 S.ringStructureSheaf.obj)
  letI : PreservesFiniteCoproducts U := by
    dsimp [U]
    infer_instance
  letI : PreservesFiniteCoproducts T := by
    change PreservesFiniteCoproducts
      (MonoidalCategory.tensorLeft
        (C := PresheafOfModules
          (S.structureSheaf.obj ⋙ forget₂ CommRingCat RingCat))
        (show PresheafOfModules
          (S.structureSheaf.obj ⋙ forget₂ CommRingCat RingCat) from P))
    infer_instance
  letI : PreservesFiniteCoproducts H := by
    dsimp [H]
    infer_instance
  change PreservesFiniteCoproducts (U ⋙ T ⋙ H)
  infer_instance

set_option linter.style.haveILetI false in
omit [∀ X, HasWeakSheafify (S.topology.over X) AddCommGrpCat.{w}]
  [∀ X, (S.topology.over X).WEqualsLocallyBijective AddCommGrpCat.{w}] in
theorem tensorRightFunctor_preservesFiniteCoproducts (M : S.Modules) :
    PreservesFiniteCoproducts (tensorRightUnderlyingFunctor S M) := by
  exact tensorSheafificationRightFunctor_preservesFiniteCoproducts S M.val

/-- Tensoring actual sheaf isomorphisms gives an isomorphism for the existing sheafified tensor. -/
noncomputable def tensorMapIso {L L' M M' : S.Modules}
    (eL : L ≅ L') (eM : M ≅ M') :
    (tensor S).obj (L, M) ≅ (tensor S).obj (L', M') := by
  letI : Presheaf.IsLocallyInjective S.topology
      (𝟙 S.ringStructureSheaf.obj) := inferInstance
  letI : Presheaf.IsLocallySurjective S.topology
      (𝟙 S.ringStructureSheaf.obj) := inferInstance
  letI : MonoidalCategory (PresheafOfModules S.ringStructureSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := S.structureSheaf.obj)
  exact (moduleSheafification S).mapIso
    (tensorIso ((SheafOfModules.forget S.ringStructureSheaf).mapIso eL)
      ((SheafOfModules.forget S.ringStructureSheaf).mapIso eM))

/-- Sheafifying `P ⊗ N` and tensoring `N` with the sheafification of `P` are related by the
canonical map obtained by applying sheafification to `η P ⊗ 𝟙 N`. -/
noncomputable def tensorSheafificationRightComparison
    (P : PresheafOfModules S.ringStructureSheaf.obj) (N : S.Modules) :
    (moduleSheafification S).obj (modulePresheafTensor S P N.val) ⟶
      (tensor S).obj ((moduleSheafification S).obj P, N) := by
  letI : Presheaf.IsLocallyInjective S.topology
      (𝟙 S.ringStructureSheaf.obj) := inferInstance
  letI : Presheaf.IsLocallySurjective S.topology
      (𝟙 S.ringStructureSheaf.obj) := inferInstance
  letI : MonoidalCategory (PresheafOfModules S.ringStructureSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := S.structureSheaf.obj)
  let sh := PresheafOfModules.sheafification
    (R₀ := S.ringStructureSheaf.obj) (R := S.ringStructureSheaf)
      (𝟙 S.ringStructureSheaf.obj)
  change sh.obj (modulePresheafTensor S P N.val) ⟶
    sh.obj (modulePresheafTensor S (sh.obj P).val N.val)
  exact sh.map
    (((PresheafOfModules.sheafificationAdjunction
      (R₀ := S.ringStructureSheaf.obj) (R := S.ringStructureSheaf)
      (𝟙 S.ringStructureSheaf.obj)).unit.app P) ⊗ₘ 𝟙 N.val)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
omit [∀ X, HasWeakSheafify (S.topology.over X) AddCommGrpCat.{w}]
  [∀ X, (S.topology.over X).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Naturality of the comparison in the sheaf factor.  This is the square used to transport the
unit calculation through finite free coproduct presentations. -/
theorem tensorSheafificationRightComparison_naturality
    (P : PresheafOfModules S.ringStructureSheaf.obj)
    {N N' : S.Modules} (f : N ⟶ N') :
    tensorSheafificationRightComparison S P N ≫
        (tensorRightFunctor S ((moduleSheafification S).obj P)).map f =
      (tensorSheafificationRightFunctor S P).map f ≫
        tensorSheafificationRightComparison S P N' := by
  letI : Presheaf.IsLocallyInjective S.topology
      (𝟙 S.ringStructureSheaf.obj) := inferInstance
  letI : Presheaf.IsLocallySurjective S.topology
      (𝟙 S.ringStructureSheaf.obj) := inferInstance
  letI : MonoidalCategory (PresheafOfModules S.ringStructureSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := S.structureSheaf.obj)
  let sh := moduleSheafification S
  let η := (PresheafOfModules.sheafificationAdjunction
    (R₀ := S.ringStructureSheaf.obj) (R := S.ringStructureSheaf)
      (𝟙 S.ringStructureSheaf.obj)).unit.app P
  dsimp [tensorSheafificationRightComparison, tensorRightFunctor,
    tensorSheafificationRightFunctor, Functor.curryObj]
  change sh.map (η ⊗ₘ 𝟙 N.val) ≫
      sh.map (𝟙 (sh.obj P).val ⊗ₘ f.val) =
    sh.map (𝟙 P ⊗ₘ f.val) ≫ sh.map (η ⊗ₘ 𝟙 N'.val)
  conv_lhs => rw [← sh.map_comp]
  conv_rhs => rw [← sh.map_comp]
  congr 1
  exact (MonoidalCategory.whisker_exchange η f.val).symm

noncomputable def tensorSheafificationRightComparisonNatTrans
    (P : PresheafOfModules S.ringStructureSheaf.obj) :
    tensorSheafificationRightFunctor S P ⟶
      tensorRightFunctor S ((moduleSheafification S).obj P) where
  app N := tensorSheafificationRightComparison S P N
  naturality _ _ f := (tensorSheafificationRightComparison_naturality S P f).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
omit [∀ X, HasWeakSheafify (S.topology.over X) AddCommGrpCat.{w}]
  [∀ X, (S.topology.over X).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Tensoring a presheaf with the structure sheaf gives an invertible comparison. -/
theorem tensorSheafificationRightComparison_unit_isIso
    (P : PresheafOfModules S.ringStructureSheaf.obj) :
    IsIso (tensorSheafificationRightComparison S P (tensorUnit S)) := by
  letI : Presheaf.IsLocallyInjective S.topology
      (𝟙 S.ringStructureSheaf.obj) := inferInstance
  letI : Presheaf.IsLocallySurjective S.topology
      (𝟙 S.ringStructureSheaf.obj) := inferInstance
  letI : MonoidalCategory (PresheafOfModules S.ringStructureSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := S.structureSheaf.obj)
  let sh := PresheafOfModules.sheafification
    (R₀ := S.ringStructureSheaf.obj) (R := S.ringStructureSheaf)
      (𝟙 S.ringStructureSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction
    (R₀ := S.ringStructureSheaf.obj) (R := S.ringStructureSheaf)
      (𝟙 S.ringStructureSheaf.obj)
  let η := adj.unit.app P
  have hnat : (η ⊗ₘ 𝟙 (tensorUnit S).val) ≫
      (rightUnitor (sh.obj P).val).hom =
      (rightUnitor P).hom ≫ η :=
    rightUnitor_naturality η
  have hfac : tensorSheafificationRightComparison S P (tensorUnit S) ≫
      (tensorRightUnitIso S (sh.obj P)).hom = sh.map (rightUnitor P).hom := by
    dsimp [tensorSheafificationRightComparison, tensorRightUnitIso]
    change sh.map (η ⊗ₘ 𝟙 (tensorUnit S).val) ≫
        sh.map (rightUnitor (sh.obj P).val).hom ≫ adj.counit.app (sh.obj P) =
      sh.map (rightUnitor P).hom
    rw [← Category.assoc, ← sh.map_comp, hnat, sh.map_comp, Category.assoc,
      adj.left_triangle_components, Category.comp_id]
  letI : IsIso (tensorRightUnitIso S (sh.obj P)).hom :=
    (tensorRightUnitIso S (sh.obj P)).isIso_hom
  letI : IsIso (sh.map (rightUnitor P).hom) := by
    infer_instance
  exact IsIso.of_isIso_fac_right hfac

set_option linter.style.haveILetI false in
omit [∀ X, HasWeakSheafify (S.topology.over X) AddCommGrpCat.{w}]
  [∀ X, (S.topology.over X).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The comparison is invertible for every finite free sheaf factor.  This follows by presenting
the free sheaf as a finite coproduct of copies of the unit and applying the colimit-point
isomorphism theorem to the comparison natural transformation. -/
theorem tensorSheafificationRightComparison_free_isIso
    (P : PresheafOfModules S.ringStructureSheaf.obj)
    (I : Type w) [Finite I] :
    IsIso (tensorSheafificationRightComparison S P
      (SheafOfModules.free (R := S.ringStructureSheaf) I)) := by
  let F := tensorSheafificationRightFunctor S P
  let G := tensorRightFunctor S ((moduleSheafification S).obj P)
  let α := tensorSheafificationRightComparisonNatTrans S P
  haveI : PreservesFiniteCoproducts F := by
    dsimp [F]
    exact tensorSheafificationRightFunctor_preservesFiniteCoproducts S P
  haveI : PreservesFiniteCoproducts G := by
    dsimp [G]
    rw [tensorRightFunctor_eq_underlying S]
    exact tensorRightFunctor_preservesFiniteCoproducts S ((moduleSheafification S).obj P)
  let K : Discrete I ⥤ S.Modules :=
    Discrete.functor (fun _ : I => tensorUnit S)
  letI : ∀ j : Discrete I, IsIso ((Functor.whiskerLeft K α).app j) := by
    intro j
    dsimp [K, α, tensorSheafificationRightComparisonNatTrans]
    exact tensorSheafificationRightComparison_unit_isIso S P
  letI : IsIso (Functor.whiskerLeft K α) := NatIso.isIso_of_isIso_app _
  change IsIso (α.app (SheafOfModules.free (R := S.ringStructureSheaf) I))
  exact Limits.isIso_app_coconePt_of_preservesColimit K α
    (SheafOfModules.freeCofan (R := S.ringStructureSheaf) I)
    (SheafOfModules.isColimitFreeCofan (R := S.ringStructureSheaf) I)

set_option linter.style.haveILetI false in
omit [∀ X, HasWeakSheafify (S.topology.over X) AddCommGrpCat.{w}]
  [∀ X, (S.topology.over X).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The comparison is invertible for the canonical finite free module of every rank. -/
theorem tensorSheafificationRightComparison_freeOfRank_isIso
    (P : PresheafOfModules S.ringStructureSheaf.obj) (r : ℕ) :
    IsIso (tensorSheafificationRightComparison S P (freeOfRank S r)) := by
  exact tensorSheafificationRightComparison_free_isIso S P (ULift.{w} (Fin r))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.style.haveILetI false in
omit [∀ X, HasWeakSheafify (S.topology.over X) AddCommGrpCat.{w}]
  [∀ X, (S.topology.over X).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The comparison is invariant under replacing its sheaf factor by an isomorphic module. -/
theorem tensorSheafificationRightComparison_isIso_of_iso
    (P : PresheafOfModules S.ringStructureSheaf.obj)
    {N N' : S.Modules} (e : N ≅ N')
    [IsIso (tensorSheafificationRightComparison S P N')] :
    IsIso (tensorSheafificationRightComparison S P N) := by
  letI : Presheaf.IsLocallyInjective S.topology
      (𝟙 S.ringStructureSheaf.obj) := inferInstance
  letI : Presheaf.IsLocallySurjective S.topology
      (𝟙 S.ringStructureSheaf.obj) := inferInstance
  letI : MonoidalCategory (PresheafOfModules S.ringStructureSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := S.structureSheaf.obj)
  let sh := moduleSheafification S
  let η := (PresheafOfModules.sheafificationAdjunction
    (R₀ := S.ringStructureSheaf.obj) (R := S.ringStructureSheaf)
      (𝟙 S.ringStructureSheaf.obj)).unit.app P
  let rightMap := sh.map (𝟙 (sh.obj P).val ⊗ₘ e.hom.val)
  let leftMap := sh.map (𝟙 P ⊗ₘ e.hom.val)
  have hfac : tensorSheafificationRightComparison S P N ≫ rightMap =
      leftMap ≫ tensorSheafificationRightComparison S P N' := by
    dsimp [tensorSheafificationRightComparison, rightMap, leftMap]
    change sh.map (η ⊗ₘ 𝟙 N.val) ≫
        sh.map (𝟙 (sh.obj P).val ⊗ₘ e.hom.val) =
      sh.map (𝟙 P ⊗ₘ e.hom.val) ≫ sh.map (η ⊗ₘ 𝟙 N'.val)
    conv_lhs => rw [← sh.map_comp]
    conv_rhs => rw [← sh.map_comp]
    congr 1
    exact (MonoidalCategory.whisker_exchange η e.hom.val).symm
  letI : IsIso e.hom.val := by
    change IsIso ((SheafOfModules.forget S.ringStructureSheaf).map e.hom)
    infer_instance
  letI : IsIso rightMap := by
    dsimp only [rightMap]
    infer_instance
  letI : IsIso leftMap := by
    dsimp only [leftMap]
    infer_instance
  haveI : IsIso (leftMap ≫ tensorSheafificationRightComparison S P N') :=
    inferInstance
  exact IsIso.of_isIso_fac_right hfac

/-- Internal transport of the presheaf associator, used after proving invertibility of the two
sheafification comparisons. -/
private noncomputable def tensorAssociatorOfComparisons
    (L M N : S.Modules)
    [IsIso (tensorSheafificationRightComparison S (modulePresheafTensor S L.val M.val) N)]
    [IsIso (tensorSheafificationRightComparison S (modulePresheafTensor S M.val N.val) L)] :
    (tensor S).obj ((tensor S).obj (L, M), N) ≅
      (tensor S).obj (L, (tensor S).obj (M, N)) := by
  letI : Presheaf.IsLocallyInjective S.topology
      (𝟙 S.ringStructureSheaf.obj) := inferInstance
  letI : Presheaf.IsLocallySurjective S.topology
      (𝟙 S.ringStructureSheaf.obj) := inferInstance
  letI : MonoidalCategory (PresheafOfModules S.ringStructureSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := S.structureSheaf.obj)
  letI : SymmetricCategory (PresheafOfModules S.ringStructureSheaf.obj) :=
    PresheafOfModules.symmetricCategory (R := S.structureSheaf.obj)
  let cLeft := tensorSheafificationRightComparison S
    (modulePresheafTensor S L.val M.val) N
  let cRight := tensorSheafificationRightComparison S
    (modulePresheafTensor S M.val N.val) L
  letI : IsIso cLeft := inferInstance
  let hRight : IsIso cRight := by
    dsimp [cRight]
    infer_instance
  let sh := moduleSheafification S
  change sh.obj (modulePresheafTensor S ((sh.obj (modulePresheafTensor S L.val M.val)).val)
      N.val) ≅
    sh.obj (modulePresheafTensor S L.val
      ((sh.obj (modulePresheafTensor S M.val N.val)).val))
  exact (@asIso _ _ _ _ cLeft inferInstance).symm |>.trans
    ((moduleSheafification S).mapIso
      (associator L.val M.val N.val)) |>.trans
    ((moduleSheafification S).mapIso
      (braiding L.val (modulePresheafTensor S M.val N.val))) |>.trans
    (@asIso _ _ _ _ cRight hRight) |>.trans
    (tensorSymmetry S ((moduleSheafification S).obj (modulePresheafTensor S M.val N.val)) L)

set_option linter.style.haveILetI false in
omit [∀ X, HasWeakSheafify (S.topology.over X) AddCommGrpCat.{w}]
  [∀ X, (S.topology.over X).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- A genuine associator for modules whose two outer factors carry explicit finite free
trivialisations.  The middle factor is arbitrary; the two comparison maps needed to transport
the presheaf associator are proved invertible by the finite-coproduct presentation of free. -/
noncomputable def tensorAssociator_of_iso_freeOfRank
    (L M N : S.Modules) (rL rN : ℕ)
    (eL : L ≅ freeOfRank S rL) (eN : N ≅ freeOfRank S rN) :
    (tensor S).obj ((tensor S).obj (L, M), N) ≅
      (tensor S).obj (L, (tensor S).obj (M, N)) := by
  letI : IsIso (tensorSheafificationRightComparison S
      (modulePresheafTensor S L.val M.val) N) := by
    letI : IsIso (tensorSheafificationRightComparison S
        (modulePresheafTensor S L.val M.val) (freeOfRank S rN)) :=
      tensorSheafificationRightComparison_freeOfRank_isIso S _ rN
    exact tensorSheafificationRightComparison_isIso_of_iso S _ eN
  letI : IsIso (tensorSheafificationRightComparison S
      (modulePresheafTensor S M.val N.val) L) := by
    letI : IsIso (tensorSheafificationRightComparison S
        (modulePresheafTensor S M.val N.val) (freeOfRank S rL)) :=
      tensorSheafificationRightComparison_freeOfRank_isIso S _ rL
    exact tensorSheafificationRightComparison_isIso_of_iso S _ eL
  exact tensorAssociatorOfComparisons S L M N

set_option linter.style.haveILetI false in
omit [∀ X, HasWeakSheafify (S.topology.over X) AddCommGrpCat.{w}]
  [∀ X, (S.topology.over X).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The comparison is invertible when the sheaf factor is globally the rank-one free module. -/
theorem tensorSheafificationRightComparison_freeRankOne_isIso
    (P : PresheafOfModules S.ringStructureSheaf.obj) :
    IsIso (tensorSheafificationRightComparison S P (freeOfRank S 1)) := by
  letI : IsIso (tensorSheafificationRightComparison S P (tensorUnit S)) := by
    exact tensorSheafificationRightComparison_unit_isIso S P
  exact tensorSheafificationRightComparison_isIso_of_iso S P
    (freeOfRankOneIsoTensorUnit S)

set_option linter.style.haveILetI false in
omit [∀ X, HasWeakSheafify (S.topology.over X) AddCommGrpCat.{w}]
  [∀ X, (S.topology.over X).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The comparison is transported across an actual isomorphism to the rank-one free module. -/
theorem tensorSheafificationRightComparison_isIso_of_iso_freeRankOne
    (P : PresheafOfModules S.ringStructureSheaf.obj)
    {N : S.Modules} (e : N ≅ freeOfRank S 1) :
    IsIso (tensorSheafificationRightComparison S P N) := by
  letI : IsIso (tensorSheafificationRightComparison S P (freeOfRank S 1)) := by
    exact tensorSheafificationRightComparison_freeRankOne_isIso S P
  exact tensorSheafificationRightComparison_isIso_of_iso S P e

/-- The tensor of two globally trivial rank-one modules has a canonical globally trivial rank-one
isomorphism. -/
noncomputable def freeRankOneTensorIso :
    (tensor S).obj (freeOfRank S 1, freeOfRank S 1) ≅ freeOfRank S 1 :=
  tensorMapIso S (freeOfRankOneIsoTensorUnit S) (freeOfRankOneIsoTensorUnit S) ≪≫
    tensorLeftUnitIso S (tensorUnit S) ≪≫
    (freeOfRankOneIsoTensorUnit S).symm

/-- Explicitly chosen global rank-one trivialisations are stable under the existing sheafified
tensor. -/
noncomputable def tensorIsoFreeRankOne
    {L M : S.Modules} (eL : L ≅ freeOfRank S 1) (eM : M ≅ freeOfRank S 1) :
    (tensor S).obj (L, M) ≅ freeOfRank S 1 :=
  tensorMapIso S eL eM ≪≫ freeRankOneTensorIso S

set_option linter.style.haveILetI false in
/-- A genuine associator for modules carrying explicit global rank-one free
trivialisations.  Its proof is the presheaf associator transported through the two proved
sheafification comparisons and the presheaf symmetry. -/
noncomputable def tensorAssociator_of_iso_freeRankOne
    (L M N : S.Modules)
    (eL : L ≅ freeOfRank S 1) (eN : N ≅ freeOfRank S 1) :
    (tensor S).obj ((tensor S).obj (L, M), N) ≅
      (tensor S).obj (L, (tensor S).obj (M, N)) := by
  letI : IsIso (tensorSheafificationRightComparison S
      (modulePresheafTensor S L.val M.val) N) := by
    exact tensorSheafificationRightComparison_isIso_of_iso_freeRankOne S _ eN
  letI : IsIso (tensorSheafificationRightComparison S
      (modulePresheafTensor S M.val N.val) L) := by
    exact tensorSheafificationRightComparison_isIso_of_iso_freeRankOne S _ eL
  exact tensorAssociatorOfComparisons S L M N

set_option linter.style.haveILetI false in
omit [∀ X, HasWeakSheafify (S.topology.over X) AddCommGrpCat.{w}]
  [∀ X, (S.topology.over X).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Applying the tensor symmetry twice gives the identity, for arbitrary module sheaves. -/
@[simp] theorem tensorSymmetry_involutive (M N : S.Modules) :
    (tensorSymmetry S M N).hom ≫ (tensorSymmetry S N M).hom =
      𝟙 ((tensor S).obj (M, N)) := by
  letI : MonoidalCategory (PresheafOfModules S.ringStructureSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := S.structureSheaf.obj)
  letI : SymmetricCategory (PresheafOfModules S.ringStructureSheaf.obj) :=
    PresheafOfModules.symmetricCategory (R := S.structureSheaf.obj)
  change (moduleSheafification S).map (β_ M.val N.val).hom ≫
      (moduleSheafification S).map (β_ N.val M.val).hom = _
  rw [← Functor.map_comp]
  simp
  rfl

set_option linter.style.haveILetI false in
omit [∀ X, HasWeakSheafify (S.topology.over X) AddCommGrpCat.{w}]
  [∀ X, (S.topology.over X).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The tensor symmetry commutes with morphisms in both module variables. -/
theorem tensorSymmetry_naturality {M M' N N' : S.Modules}
    (f : M ⟶ M') (g : N ⟶ N') :
    (tensor S).map (f, g) ≫ (tensorSymmetry S M' N').hom =
      (tensorSymmetry S M N).hom ≫ (tensor S).map (g, f) := by
  letI : MonoidalCategory (PresheafOfModules S.ringStructureSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := S.structureSheaf.obj)
  letI : SymmetricCategory (PresheafOfModules S.ringStructureSheaf.obj) :=
    PresheafOfModules.symmetricCategory (R := S.structureSheaf.obj)
  change (moduleSheafification S).map (f.val ⊗ₘ g.val) ≫
      (moduleSheafification S).map (β_ M'.val N'.val).hom =
    (moduleSheafification S).map (β_ M.val N.val).hom ≫
      (moduleSheafification S).map (g.val ⊗ₘ f.val)
  rw [← Functor.map_comp, ← Functor.map_comp, braiding_naturality]

end TensorCoherence

end GromovWitten.AlgebraicGeometry.Modules
