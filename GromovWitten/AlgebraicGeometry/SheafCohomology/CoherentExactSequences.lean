/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.FinitePresentationLocality
import GromovWitten.AlgebraicGeometry.Curves.AffineFinitePresentation
import GromovWitten.AlgebraicGeometry.Curves.FinitePushforward
import GromovWitten.AlgebraicGeometry.SheafCohomology.AffineSectionsExact
import GromovWitten.AlgebraicGeometry.SheafCohomology.QuasiCoherentHomology
import GromovWitten.AlgebraicGeometry.SheafCohomology.QuasiCoherentKernels
import GromovWitten.AlgebraicGeometry.SheafCohomology.QuasiCoherentExtensions
import GromovWitten.CategoryTheory.FiveTermExact

/-!
# Finite presentation and exact sequences

Finite presentation is closed under short exact extensions on locally Noetherian
schemes.  The kernel and cokernel results use only the indicated weak
quasicoherence hypotheses, and the five-term result packages them into the
corresponding middle-term closure statement.
-/

open CategoryTheory Limits AlgebraicGeometry
open _root_.AlgebraicGeometry
open GromovWitten.AlgebraicGeometry.Curves
open GromovWitten.AlgebraicGeometry.SheafCohomology

noncomputable section
universe u

namespace GromovWitten.AlgebraicGeometry.SheafCohomology

variable {R : CommRingCat.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- On a Noetherian affine spectrum, finite presentation is closed under short
exact extensions of module sheaves. -/
theorem isFinitePresentation_middle_of_shortExact_of_spec
    [IsNoetherianRing R]
    (S : ShortComplex (Spec (CommRingCat.of (R : Type u))).Modules)
    (hS : S.ShortExact)
    [S.X₁.IsFinitePresentation] [S.X₃.IsFinitePresentation] :
    S.X₂.IsFinitePresentation := by
  have hX₂qc : S.X₂.IsQuasicoherent :=
    isQuasicoherent_middle_of_shortExact_of_spec S hS
  let _ : S.X₂.IsQuasicoherent := hX₂qc
  have hΓ :
      (S.map (moduleSpecΓFunctor (R := R))).ShortExact :=
    moduleSpecΓFunctor_map_shortExact_of_isQuasicoherent S hS
  let _ : Module.FinitePresentation R
      ((moduleSpecΓFunctor.obj S.X₁ : Type u)) :=
    moduleSpecΓ_isFinitePresentation S.X₁
  let _ : Module.FinitePresentation R
      ((moduleSpecΓFunctor.obj S.X₃ : Type u)) :=
    moduleSpecΓ_isFinitePresentation S.X₃
  have hΓexact : Function.Exact
      ((moduleSpecΓFunctor (R := R)).map S.f)
      ((moduleSpecΓFunctor (R := R)).map S.g) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (S.map (moduleSpecΓFunctor (R := R)))).mp hΓ.exact
  have hΓsurj : Function.Surjective
      ((moduleSpecΓFunctor (R := R)).map S.g) :=
    ShortComplex.ShortExact.moduleCat_surjective_g hΓ
  let _ : Module.Finite R ((moduleSpecΓFunctor.obj S.X₂ : Type u)) :=
    Module.Finite.of_exact hΓexact hΓsurj
  let _ : Module.FinitePresentation R
      ((moduleSpecΓFunctor.obj S.X₂ : Type u)) :=
    Module.finitePresentation_of_finite R _
  let _ : IsIso S.X₂.fromTildeΓ :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent S.X₂
  exact spec_module_isFinitePresentation S.X₂

set_option backward.isDefEq.respectTransparency false in
/-- On a Noetherian affine spectrum, a finitely presented middle term and a
quasicoherent right term force finite presentation of the left term. -/
theorem isFinitePresentation_left_of_shortExact_of_spec
    [IsNoetherianRing R]
    (S : ShortComplex (Spec (CommRingCat.of (R : Type u))).Modules)
    (hS : S.ShortExact)
    [S.X₂.IsFinitePresentation]
    [S.X₃.IsQuasicoherent] :
    S.X₁.IsFinitePresentation := by
  let _ : Mono S.f := hS.mono_f
  have hX₂qc : S.X₂.IsQuasicoherent := inferInstance
  let _ : S.X₂.IsQuasicoherent := hX₂qc
  have hX₁qc : S.X₁.IsQuasicoherent :=
    isQuasicoherent_left_of_exact S hS.exact
  let _ : S.X₁.IsQuasicoherent := hX₁qc
  have hΓ :
      (S.map (moduleSpecΓFunctor (R := R))).ShortExact :=
    moduleSpecΓFunctor_map_shortExact_of_isQuasicoherent S hS
  let _ : Module.FinitePresentation R
      ((moduleSpecΓFunctor.obj S.X₂ : Type u)) :=
    moduleSpecΓ_isFinitePresentation S.X₂
  let _ : Module.Finite R ((moduleSpecΓFunctor.obj S.X₁ : Type u)) :=
    Module.Finite.of_injective
      ((moduleSpecΓFunctor (R := R)).map S.f).hom
      (ShortComplex.ShortExact.moduleCat_injective_f hΓ)
  let _ : Module.FinitePresentation R
      ((moduleSpecΓFunctor.obj S.X₁ : Type u)) :=
    Module.finitePresentation_of_finite R _
  let _ : IsIso S.X₁.fromTildeΓ :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent S.X₁
  exact spec_module_isFinitePresentation S.X₁

set_option backward.isDefEq.respectTransparency false in
/-- On a Noetherian affine spectrum, a quasicoherent left term and a finitely
presented middle term force finite presentation of the right term. -/
theorem isFinitePresentation_right_of_shortExact_of_spec
    [IsNoetherianRing R]
    (S : ShortComplex (Spec (CommRingCat.of (R : Type u))).Modules)
    (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsFinitePresentation] :
    S.X₃.IsFinitePresentation := by
  have hX₂qc : S.X₂.IsQuasicoherent := inferInstance
  let _ : S.X₂.IsQuasicoherent := hX₂qc
  have hX₃qc : S.X₃.IsQuasicoherent := by
    have hcoqc : (cokernel S.f).IsQuasicoherent :=
      isQuasicoherent_cokernel S.f
    let _ : (cokernel S.f).IsQuasicoherent := hcoqc
    let e : S.X₃ ≅ cokernel S.f :=
      hS.gIsCokernel.coconePointUniqueUpToIso (colimit.isColimit _)
    exact (SheafOfModules.isQuasicoherent
      (Spec (CommRingCat.of (R : Type u))).ringCatSheaf).prop_of_iso
      e.symm inferInstance
  let _ : S.X₃.IsQuasicoherent := hX₃qc
  have hΓ :
      (S.map (moduleSpecΓFunctor (R := R))).ShortExact :=
    moduleSpecΓFunctor_map_shortExact_of_isQuasicoherent S hS
  let _ : Module.FinitePresentation R
      ((moduleSpecΓFunctor.obj S.X₂ : Type u)) :=
    moduleSpecΓ_isFinitePresentation S.X₂
  let _ : Module.Finite R ((moduleSpecΓFunctor.obj S.X₃ : Type u)) :=
    Module.Finite.of_surjective
      ((moduleSpecΓFunctor (R := R)).map S.g).hom
      (ShortComplex.ShortExact.moduleCat_surjective_g hΓ)
  let _ : Module.FinitePresentation R
      ((moduleSpecΓFunctor.obj S.X₃ : Type u)) :=
    Module.finitePresentation_of_finite R _
  let _ : IsIso S.X₃.fromTildeΓ :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent S.X₃
  exact spec_module_isFinitePresentation S.X₃

end GromovWitten.AlgebraicGeometry.SheafCohomology

namespace GromovWitten.AlgebraicGeometry.SheafCohomology
set_option backward.isDefEq.respectTransparency false in
/-- Finite presentation is closed under extensions on affine locally Noetherian schemes. -/
lemma isFinitePresentation_middle_of_shortExact_of_isAffine
    {X : Scheme.{u}} [IsAffine X] [IsLocallyNoetherian X]
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₁.IsFinitePresentation] [S.X₃.IsFinitePresentation] : S.X₂.IsFinitePresentation := by
  let p := X.isoSpec.inv
  let F := Scheme.Modules.pullback p
  let _ : F.PreservesHomology := moduleFlatPullback_preservesHomology p
  let _ : PreservesFiniteLimits F := F.preservesFiniteLimits_of_preservesHomology
  let _ : PreservesFiniteColimits F := F.preservesFiniteColimits_of_preservesHomology
  have hSF : (S.map F).ShortExact := hS.map_of_exact F
  let _ : IsNoetherianRing (affineGlobalRing X) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  have : (S.map F).X₁.IsFinitePresentation := by
    change (F.obj S.X₁).IsFinitePresentation
    dsimp only [F]
    infer_instance
  have : (S.map F).X₃.IsFinitePresentation := by
    change (F.obj S.X₃).IsFinitePresentation
    dsimp only [F]
    infer_instance
  have hmid : (F.obj S.X₂).IsFinitePresentation :=
    isFinitePresentation_middle_of_shortExact_of_spec (S.map F) hSF
  let G := Scheme.Modules.pullback X.isoSpec.hom
  have hback : (G.obj (F.obj S.X₂)).IsFinitePresentation := by
    dsimp only [G]
    infer_instance
  let e : F ⋙ G ≅ 𝟭 X.Modules :=
    Scheme.Modules.pullbackComp X.isoSpec.hom X.isoSpec.inv ≪≫
      Scheme.Modules.pullbackCongr X.isoSpec.hom_inv_id ≪≫ Scheme.Modules.pullbackId X
  exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso (e.app S.X₂) hback

set_option backward.isDefEq.respectTransparency false in
/-- Finite presentation is closed under extensions on a locally Noetherian scheme. -/
lemma isFinitePresentation_middle_of_shortExact
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₁.IsFinitePresentation] [S.X₃.IsFinitePresentation] : S.X₂.IsFinitePresentation := by
  apply module_isFinitePresentation_of_affine_pullbacks S.X₂
  intro U
  let _ : IsAffine U.1.toScheme := U.2
  let F := Scheme.Modules.pullback U.1.ι
  let _ : F.PreservesHomology := moduleFlatPullback_preservesHomology U.1.ι
  let _ : PreservesFiniteLimits F := F.preservesFiniteLimits_of_preservesHomology
  let _ : PreservesFiniteColimits F := F.preservesFiniteColimits_of_preservesHomology
  have hSF : (S.map F).ShortExact := hS.map_of_exact F
  have : (S.map F).X₁.IsFinitePresentation := by
    change (F.obj S.X₁).IsFinitePresentation
    dsimp only [F]
    infer_instance
  have : (S.map F).X₃.IsFinitePresentation := by
    change (F.obj S.X₃).IsFinitePresentation
    dsimp only [F]
    infer_instance
  exact isFinitePresentation_middle_of_shortExact_of_isAffine (S.map F) hSF
set_option backward.isDefEq.respectTransparency false in
/-- Finite presentation of the middle term and quasicoherence on the right give
finite presentation on the left over an affine locally Noetherian scheme. -/
lemma isFinitePresentation_left_of_shortExact_of_isAffine
    {X : Scheme.{u}} [IsAffine X] [IsLocallyNoetherian X]
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₂.IsFinitePresentation] [S.X₃.IsQuasicoherent] : S.X₁.IsFinitePresentation := by
  let p := X.isoSpec.inv
  let F := Scheme.Modules.pullback p
  let _ : F.PreservesHomology := moduleFlatPullback_preservesHomology p
  let _ : PreservesFiniteLimits F := F.preservesFiniteLimits_of_preservesHomology
  let _ : PreservesFiniteColimits F := F.preservesFiniteColimits_of_preservesHomology
  have hSF : (S.map F).ShortExact := hS.map_of_exact F
  let _ : IsNoetherianRing (affineGlobalRing X) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  have : (S.map F).X₂.IsFinitePresentation := by
    change (F.obj S.X₂).IsFinitePresentation
    dsimp only [F]
    infer_instance
  have : (S.map F).X₃.IsQuasicoherent := by
    change (F.obj S.X₃).IsQuasicoherent
    dsimp only [F]
    infer_instance
  have hmid : (F.obj S.X₁).IsFinitePresentation :=
    isFinitePresentation_left_of_shortExact_of_spec (S.map F) hSF
  let G := Scheme.Modules.pullback X.isoSpec.hom
  have hback : (G.obj (F.obj S.X₁)).IsFinitePresentation := by
    dsimp only [G]
    infer_instance
  let e : F ⋙ G ≅ 𝟭 X.Modules :=
    Scheme.Modules.pullbackComp X.isoSpec.hom X.isoSpec.inv ≪≫
      Scheme.Modules.pullbackCongr X.isoSpec.hom_inv_id ≪≫ Scheme.Modules.pullbackId X
  exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso (e.app S.X₁) hback

set_option backward.isDefEq.respectTransparency false in
/-- Finite presentation of the middle term and quasicoherence on the right give
finite presentation on the left over a locally Noetherian scheme. -/
lemma isFinitePresentation_left_of_shortExact
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₂.IsFinitePresentation] [S.X₃.IsQuasicoherent] : S.X₁.IsFinitePresentation := by
  apply module_isFinitePresentation_of_affine_pullbacks S.X₁
  intro U
  let _ : IsAffine U.1.toScheme := U.2
  let F := Scheme.Modules.pullback U.1.ι
  let _ : F.PreservesHomology := moduleFlatPullback_preservesHomology U.1.ι
  let _ : PreservesFiniteLimits F := F.preservesFiniteLimits_of_preservesHomology
  let _ : PreservesFiniteColimits F := F.preservesFiniteColimits_of_preservesHomology
  have hSF : (S.map F).ShortExact := hS.map_of_exact F
  have : (S.map F).X₂.IsFinitePresentation := by
    change (F.obj S.X₂).IsFinitePresentation
    dsimp only [F]
    infer_instance
  have : (S.map F).X₃.IsQuasicoherent := by
    change (F.obj S.X₃).IsQuasicoherent
    dsimp only [F]
    infer_instance
  exact isFinitePresentation_left_of_shortExact_of_isAffine (S.map F) hSF
set_option backward.isDefEq.respectTransparency false in
/-- A quasicoherent left term and finitely presented middle term give a finitely
presented right term over an affine locally Noetherian scheme. -/
lemma isFinitePresentation_right_of_shortExact_of_isAffine
    {X : Scheme.{u}} [IsAffine X] [IsLocallyNoetherian X]
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsFinitePresentation] : S.X₃.IsFinitePresentation := by
  let p := X.isoSpec.inv
  let F := Scheme.Modules.pullback p
  let _ : F.PreservesHomology := moduleFlatPullback_preservesHomology p
  let _ : PreservesFiniteLimits F := F.preservesFiniteLimits_of_preservesHomology
  let _ : PreservesFiniteColimits F := F.preservesFiniteColimits_of_preservesHomology
  have hSF : (S.map F).ShortExact := hS.map_of_exact F
  let _ : IsNoetherianRing (affineGlobalRing X) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  have : (S.map F).X₁.IsQuasicoherent := by
    change (F.obj S.X₁).IsQuasicoherent
    dsimp only [F]
    infer_instance
  have : (S.map F).X₂.IsFinitePresentation := by
    change (F.obj S.X₂).IsFinitePresentation
    dsimp only [F]
    infer_instance
  have hmid : (F.obj S.X₃).IsFinitePresentation :=
    isFinitePresentation_right_of_shortExact_of_spec (S.map F) hSF
  let G := Scheme.Modules.pullback X.isoSpec.hom
  have hback : (G.obj (F.obj S.X₃)).IsFinitePresentation := by
    dsimp only [G]
    infer_instance
  let e : F ⋙ G ≅ 𝟭 X.Modules :=
    Scheme.Modules.pullbackComp X.isoSpec.hom X.isoSpec.inv ≪≫
      Scheme.Modules.pullbackCongr X.isoSpec.hom_inv_id ≪≫ Scheme.Modules.pullbackId X
  exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso (e.app S.X₃) hback

set_option backward.isDefEq.respectTransparency false in
/-- A quasicoherent left term and finitely presented middle term give a finitely
presented right term over a locally Noetherian scheme. -/
lemma isFinitePresentation_right_of_shortExact
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsFinitePresentation] : S.X₃.IsFinitePresentation := by
  apply module_isFinitePresentation_of_affine_pullbacks S.X₃
  intro U
  let _ : IsAffine U.1.toScheme := U.2
  let F := Scheme.Modules.pullback U.1.ι
  let _ : F.PreservesHomology := moduleFlatPullback_preservesHomology U.1.ι
  let _ : PreservesFiniteLimits F := F.preservesFiniteLimits_of_preservesHomology
  let _ : PreservesFiniteColimits F := F.preservesFiniteColimits_of_preservesHomology
  have hSF : (S.map F).ShortExact := hS.map_of_exact F
  have : (S.map F).X₁.IsQuasicoherent := by
    change (F.obj S.X₁).IsQuasicoherent
    dsimp only [F]
    infer_instance
  have : (S.map F).X₂.IsFinitePresentation := by
    change (F.obj S.X₂).IsFinitePresentation
    dsimp only [F]
    infer_instance
  exact isFinitePresentation_right_of_shortExact_of_isAffine (S.map F) hSF

variable {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The kernel of a morphism from a finitely presented module to a
quasicoherent module is finitely presented on a locally Noetherian scheme. -/
theorem isFinitePresentation_kernel
    [IsLocallyNoetherian X] {M N : X.Modules} (f : M ⟶ N)
    [M.IsFinitePresentation] [N.IsQuasicoherent] :
    (kernel f).IsFinitePresentation := by
  have hKqc : (kernel f).IsQuasicoherent := isQuasicoherent_kernel f
  let _ : (kernel f).IsQuasicoherent := hKqc
  have hCqc : (cokernel (kernel.ι f)).IsQuasicoherent :=
    isQuasicoherent_cokernel (kernel.ι f)
  let _ : (cokernel (kernel.ι f)).IsQuasicoherent := hCqc
  let S : ShortComplex X.Modules := ShortComplex.cokernelSequence (kernel.ι f)
  have hS : S.ShortExact := by
    change (ShortComplex.cokernelSequence (kernel.ι f)).ShortExact
    exact
      { exact := ShortComplex.cokernelSequence_exact (kernel.ι f)
        mono_f := by
          change Mono (kernel.ι f)
          infer_instance }
  let _ : S.X₂.IsFinitePresentation := by
    change M.IsFinitePresentation
    infer_instance
  let _ : S.X₃.IsQuasicoherent := by
    change (cokernel (kernel.ι f)).IsQuasicoherent
    exact hCqc
  exact isFinitePresentation_left_of_shortExact S hS

set_option backward.isDefEq.respectTransparency false in
/-- The cokernel of a morphism from a quasicoherent module into a finitely presented module
is finitely presented on a locally Noetherian scheme. -/
theorem isFinitePresentation_cokernel
    [IsLocallyNoetherian X] {M N : X.Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsFinitePresentation] :
    (cokernel f).IsFinitePresentation := by
  have hCqc : (cokernel f).IsQuasicoherent := isQuasicoherent_cokernel f
  let _ : (cokernel f).IsQuasicoherent := hCqc
  have hKqc : (kernel (cokernel.π f)).IsQuasicoherent :=
    isQuasicoherent_kernel (cokernel.π f)
  let _ : (kernel (cokernel.π f)).IsQuasicoherent := hKqc
  let S : ShortComplex X.Modules := ShortComplex.kernelSequence (cokernel.π f)
  have hS : S.ShortExact := by
    change (ShortComplex.kernelSequence (cokernel.π f)).ShortExact
    exact
      { exact := ShortComplex.kernelSequence_exact (cokernel.π f)
        epi_g := by
          change Epi (cokernel.π f)
          infer_instance }
  let _ : S.X₁.IsQuasicoherent := by
    change (kernel (cokernel.π f)).IsQuasicoherent
    exact hKqc
  let _ : S.X₂.IsFinitePresentation := by
    change N.IsFinitePresentation
    infer_instance
  exact isFinitePresentation_right_of_shortExact S hS

set_option backward.isDefEq.respectTransparency false in
/-- In a five-term exact sequence, finitely presented interior outer terms and
quasicoherent endpoints force finite presentation of the middle object. -/
theorem isFinitePresentation_middle_of_fiveTerm
    [IsLocallyNoetherian X]
    {A B D E F : X.Modules} (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E) (k : E ⟶ F)
    (hfg : f ≫ g = 0) (hgh : g ≫ h = 0) (hhk : h ≫ k = 0)
    (he₁ : (ShortComplex.mk f g hfg).Exact)
    (he₂ : (ShortComplex.mk g h hgh).Exact)
    (he₃ : (ShortComplex.mk h k hhk).Exact)
    [A.IsQuasicoherent] [B.IsFinitePresentation]
    [E.IsFinitePresentation] [F.IsQuasicoherent] :
    D.IsFinitePresentation := by
  have hcfp : (cokernel f).IsFinitePresentation :=
    isFinitePresentation_cokernel f
  have hkfp : (kernel k).IsFinitePresentation :=
    isFinitePresentation_kernel k
  let T := ShortComplex.fiveTermShortComplex f g h k hfg hgh hhk
  let _ : T.X₁.IsFinitePresentation := by
    change (cokernel f).IsFinitePresentation
    exact hcfp
  let _ : T.X₃.IsFinitePresentation := by
    change (kernel k).IsFinitePresentation
    exact hkfp
  have hT : T.ShortExact :=
    ShortComplex.fiveTerm_shortExact f g h k hfg hgh hhk he₁ he₂ he₃
  exact isFinitePresentation_middle_of_shortExact T hT

end GromovWitten.AlgebraicGeometry.SheafCohomology
