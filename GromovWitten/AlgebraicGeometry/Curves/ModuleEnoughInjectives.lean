/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ModuleGrothendieck
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# Enough injectives for sheaves of modules on a scheme

Sheafification is a left exact reflector. Exactness of filtered colimits therefore
passes from presheaves of modules to sheaves of modules. Together with the explicit
free-Yoneda separator this makes `X.Modules` a Grothendieck abelian category, so it
has enough injectives. These instances enable the usual module-valued derived
pushforward without assuming that an injective module remains injective after
forgetting its scalar action.
-/

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

/-- Filtered colimits of sheaves of modules on a scheme are exact. -/
theorem schemeModules_hasExactColimitsOfShape (X : Scheme.{u})
    {J : Type u} [Category.{u} J] [IsFiltered J] :
    HasExactColimitsOfShape J X.Modules :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).hasExactColimitsOfShape J

/-- Sheaves of modules on a scheme form a Grothendieck abelian category. -/
instance schemeModules_isGrothendieckAbelian (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u} X.Modules where
  ab5OfSize := ⟨fun _ _ _ => schemeModules_hasExactColimitsOfShape X⟩

/-- Every sheaf of modules embeds in an injective sheaf of modules. -/
theorem schemeModules_enoughInjectives (X : Scheme.{u}) : EnoughInjectives X.Modules :=
  inferInstance

end GromovWitten.AlgebraicGeometry.Curves
