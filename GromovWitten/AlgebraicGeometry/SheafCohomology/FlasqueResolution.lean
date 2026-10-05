/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.SheafCohomology.FlasqueNatComplex
import GromovWitten.AlgebraicGeometry.SheafCohomology.ResolutionComparison
import GromovWitten.AlgebraicGeometry.SheafCohomology.ComparisonUniqueness

/-!
# Computing derived pushforward with a flasque resolution

Any resolution by flasque abelian sheaves computes the right derived pushforward.
The comparison map into an injective resolution is a quasi-isomorphism between
flasque complexes, and stays a quasi-isomorphism after pushforward.
-/

open CategoryTheory Limits HomologicalComplex

namespace TopCat.Sheaf

universe u

noncomputable section

variable {X Y : TopCat.{u}} (f : X ⟶ Y)
variable [(pushforward AddCommGrpCat.{u} f).Additive]
variable [EnoughInjectives (Sheaf AddCommGrpCat.{u} X)]

/-- A flasque resolution computes all right derived pushforwards. -/
def flasqueResolutionRightDerivedIso {F : Sheaf AddCommGrpCat.{u} X}
    {K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℕ}
    (a : (CochainComplex.single₀ _).obj F ⟶ K) [QuasiIso a]
    (hK : ∀ n, IsFlasque (K.X n)) (n : ℕ) :
    ((pushforward AddCommGrpCat f).rightDerived n).obj F ≅
      ((pushforward AddCommGrpCat f).mapHomologicalComplex (.up ℕ) |>.obj K).homology n := by
  let I := InjectiveResolution.of F
  let φ := (I.exists_desc_of_quasiIso a).choose
  have : QuasiIso φ := (I.exists_desc_of_quasiIso a).choose_spec.2
  have hI (k : ℕ) : IsFlasque (I.cocomplex.X k) := isFlasque_of_injective X _
  have := pushforward_quasiIso_of_flasque f φ hK hI
  exact I.isoRightDerivedObj (pushforward AddCommGrpCat f) n ≪≫
    (isoOfQuasiIsoAt ((pushforward AddCommGrpCat f).mapHomologicalComplex _ |>.map φ) n).symm

set_option backward.isDefEq.respectTransparency false in
/-- The flasque resolution comparison is natural in the resolved sheaf. -/
lemma flasqueResolutionRightDerivedIso_hom_naturality
    {A B : Sheaf AddCommGrpCat.{u} X}
    {K L : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℕ}
    (a : (CochainComplex.single₀ _).obj A ⟶ K) [QuasiIso a]
    (b : (CochainComplex.single₀ _).obj B ⟶ L) [QuasiIso b]
    (u : A ⟶ B)
    (φ : K ⟶ L)
    (hφ : a ≫ φ = (CochainComplex.single₀ _).map u ≫ b)
    (hK : ∀ n, IsFlasque (K.X n)) (hL : ∀ n, IsFlasque (L.X n))
    (n : ℕ) :
    ((pushforward AddCommGrpCat f).rightDerived n).map u ≫
        (flasqueResolutionRightDerivedIso f b hL n).hom =
      (flasqueResolutionRightDerivedIso f a hK n).hom ≫
        HomologicalComplex.homologyMap
          (((pushforward AddCommGrpCat f).mapHomologicalComplex (.up ℕ)).map φ) n := by
  let P := pushforward AddCommGrpCat.{u} f
  let I := InjectiveResolution.of A
  let J := InjectiveResolution.of B
  let t := (I.exists_desc_of_quasiIso a).choose
  have hta : a ≫ t = I.ι := (I.exists_desc_of_quasiIso a).choose_spec.1
  have hqt : QuasiIso t := (I.exists_desc_of_quasiIso a).choose_spec.2
  let v := (J.exists_desc_of_quasiIso b).choose
  have hbv : b ≫ v = J.ι := (J.exists_desc_of_quasiIso b).choose_spec.1
  have hqv : QuasiIso v := (J.exists_desc_of_quasiIso b).choose_spec.2
  have hcomp : a ≫ (t ≫ InjectiveResolution.desc u J I) = a ≫ (φ ≫ v) := by
    rw [← Category.assoc, hta, InjectiveResolution.desc_commutes,
      ← Category.assoc, hφ, Category.assoc, hbv]
  obtain ⟨H⟩ := CochainComplex.nonempty_homotopy_of_precomp_quasiIso_nat a
    (t ≫ InjectiveResolution.desc u J I) (φ ≫ v) hcomp
  have hH : HomologicalComplex.homologyMap
      ((P.mapHomologicalComplex (.up ℕ)).map (t ≫ InjectiveResolution.desc u J I)) n =
      HomologicalComplex.homologyMap
        ((P.mapHomologicalComplex (.up ℕ)).map (φ ≫ v)) n := by
    rw [← Homotopy.homologyMap_eq (P.mapHomotopy H) n]
  let Hn := P.mapHomologicalComplex (.up ℕ) ⋙ homologyFunctor _ (.up ℕ) n
  have hderived := InjectiveResolution.isoRightDerivedObj_hom_naturality u I J
    (InjectiveResolution.desc u J I) (InjectiveResolution.desc_commutes_zero u J I) P n
  have hI (k : ℕ) : IsFlasque (I.cocomplex.X k) := isFlasque_of_injective X _
  have hJ (k : ℕ) : IsFlasque (J.cocomplex.X k) := isFlasque_of_injective X _
  have htP : QuasiIso ((P.mapHomologicalComplex (.up ℕ)).map t) :=
    pushforward_quasiIso_of_flasque f t hK hI
  have hvP : QuasiIso ((P.mapHomologicalComplex (.up ℕ)).map v) :=
    pushforward_quasiIso_of_flasque f v hL hJ
  have hcompH :
      HomologicalComplex.homologyMap ((P.mapHomologicalComplex (.up ℕ)).map t) n ≫
          HomologicalComplex.homologyMap
            ((P.mapHomologicalComplex (.up ℕ)).map (InjectiveResolution.desc u J I)) n =
        HomologicalComplex.homologyMap ((P.mapHomologicalComplex (.up ℕ)).map φ) n ≫
          HomologicalComplex.homologyMap ((P.mapHomologicalComplex (.up ℕ)).map v) n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
    simpa only [← Functor.map_comp] using hH
  let et : Hn.obj K ≅ Hn.obj I.cocomplex :=
    isoOfQuasiIsoAt ((P.mapHomologicalComplex (.up ℕ)).map t) n
  let ev : Hn.obj L ≅ Hn.obj J.cocomplex :=
    isoOfQuasiIsoAt ((P.mapHomologicalComplex (.up ℕ)).map v) n
  have hc : et.hom ≫ Hn.map (InjectiveResolution.desc u J I) = Hn.map φ ≫ ev.hom := by
    exact hcompH
  change (P.rightDerived n).map u ≫ ((J.isoRightDerivedObj P n).hom ≫ ev.inv) =
    ((I.isoRightDerivedObj P n).hom ≫ et.inv) ≫ Hn.map φ
  simp only [Category.assoc]
  rw [← Category.assoc, hderived, Category.assoc]
  apply (cancel_epi (I.isoRightDerivedObj P n).hom).mpr
  apply (cancel_mono ev.hom).mp
  apply (cancel_epi et.hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id, Iso.hom_inv_id_assoc, Iso.hom_inv_id] using hc

end

end TopCat.Sheaf
