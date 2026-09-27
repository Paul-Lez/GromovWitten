/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.ModuleOpenBaseChange
import GromovWitten.AlgebraicGeometry.Curves.HigherBaseChange

/-!
# Higher direct-image base change along open inclusions

Open restriction preserves flasque module sheaves. Thus the restriction of an
injective module resolution computes derived pushforward. Together with ordinary
open base change, this proves that the canonical higher comparison is an
isomorphism in every degree, without a quasi-coherence hypothesis.
-/

open CategoryTheory Limits HomologicalComplex
open _root_.AlgebraicGeometry

noncomputable section

namespace GromovWitten.AlgebraicGeometry.Curves
universe u
variable {X Y : Scheme.{u}}
/-- Pushforward preserves quasi-isomorphisms between complexes of flasque module sheaves. -/
lemma modulePushforward_quasiIso_of_flasque (f : X ⟶ Y)
    {K L : CochainComplex X.Modules ℕ} (φ : K ⟶ L) [QuasiIso φ]
    (hK : ∀ n, TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj (K.X n)))
    (hL : ∀ n, TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj (L.X n))) :
    QuasiIso (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℕ)).map φ) := by
  apply (quasiIso_map_iff_of_preservesHomology _ (moduleToSheafAb Y)).mp
  exact TopCat.Sheaf.pushforward_quasiIso_of_flasque f.base
    (((moduleToSheafAb X).mapHomologicalComplex (.up ℕ)).map φ) hK hL

/-- Restriction to an open subscheme preserves flasqueness of the underlying abelian sheaf. -/
lemma moduleRestrict_isFlasque (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) [TopCat.Sheaf.IsFlasque ((moduleToSheafAb Y).obj M)] :
    TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj
      ((Scheme.Modules.restrictFunctor f).obj M)) := by
  constructor
  intro U V i
  change Epi (((moduleToSheafAb Y).obj M).obj.map
    (f.opensFunctor.map i.unop).op)
  exact TopCat.Presheaf.IsFlasque.epi (F := ((moduleToSheafAb Y).obj M).obj) _

/-- Pullback along an open immersion preserves flasqueness of the underlying abelian sheaf. -/
lemma modulePullback_isFlasque (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) [TopCat.Sheaf.IsFlasque ((moduleToSheafAb Y).obj M)] :
    TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj
      ((Scheme.Modules.pullback f).obj M)) := by
  have := moduleRestrict_isFlasque f M
  exact TopCat.Sheaf.isFlasque_of_iso
    ((moduleToSheafAb X).mapIso ((Scheme.Modules.restrictFunctorIsoPullback f).app M))

variable {Z : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false in
/-- Open pullback sends injective module resolutions to flasque resolutions, so the canonical
derived precomposition comparison is invertible. -/
lemma moduleOpenPullback_rightDerivedPrecomp_isIso
    (p : X ⟶ Y) [IsOpenImmersion p] (g : X ⟶ Z) (M : Y.Modules) (n : ℕ) :
    IsIso ((Functor.rightDerivedPrecompComparison (Scheme.Modules.pullback p)
      (Scheme.Modules.pushforward g) n).app M) := by
  let L := Scheme.Modules.pullback p
  let F := Scheme.Modules.pushforward g
  let I := injectiveResolution M
  let J := injectiveResolution (L.obj M)
  let a := (singleMapHomologicalComplex L (.up ℕ) 0).inv.app M ≫
    (L.mapHomologicalComplex (.up ℕ)).map I.ι
  have : QuasiIso a := by dsimp [a]; infer_instance
  obtain ⟨φ, hφ, hq⟩ := J.exists_desc_of_quasiIso a
  have : QuasiIso φ := hq
  have hK (k : ℕ) : TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj
      (((L.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).X k)) := by
    exact modulePullback_isFlasque p (I.cocomplex.X k)
  have hJ (k : ℕ) : TopCat.Sheaf.IsFlasque ((moduleToSheafAb X).obj
      (J.cocomplex.X k)) := module_isFlasque_of_injective _
  have : QuasiIso ((F.mapHomologicalComplex (.up ℕ)).map φ) :=
    modulePushforward_quasiIso_of_flasque g φ hK hJ
  apply Functor.rightDerivedPrecompComparison_app_isIso_of_quasiIso L F M φ _ n
  simpa only [a, Category.assoc] using hφ

set_option backward.isDefEq.respectTransparency false in
/-- The canonical higher base-change map along an open inclusion is invertible in every degree. -/
lemma moduleHigherBaseChange_open_isIso (f : X ⟶ Y) (U : Y.Opens)
    (M : X.Modules) (n : ℕ) :
    IsIso ((moduleHigherBaseChangeNatTrans f U.ι (f ⁻¹ᵁ U).ι (f ∣_ U)
      (isPullback_morphismRestrict f U).flip n).app M) := by
  let α := modulePushforwardBaseChangeNatTrans f U.ι (f ⁻¹ᵁ U).ι (f ∣_ U)
    (isPullback_morphismRestrict f U).flip
  have : IsIso α := (NatTrans.isIso_iff_isIso_app α).mpr
    (fun N => moduleBaseChange_open_isIso f U N)
  have : IsIso ((NatTrans.rightDerived α n).app M) := by
    change IsIso ((NatIso.rightDerivedIso (asIso α) n).hom.app M)
    infer_instance
  have := moduleOpenPullback_rightDerivedPrecomp_isIso (f ⁻¹ᵁ U).ι (f ∣_ U) M n
  change IsIso (((Functor.rightDerivedCompExactNatIso (Scheme.Modules.pullback U.ι)
      (Scheme.Modules.pushforward f) n).inv.app M) ≫
      (NatTrans.rightDerived α n).app M ≫
      (Functor.rightDerivedPrecompComparison (Scheme.Modules.pullback (f ⁻¹ᵁ U).ι)
        (Scheme.Modules.pushforward (f ∣_ U)) n).app M)
  infer_instance
end GromovWitten.AlgebraicGeometry.Curves
