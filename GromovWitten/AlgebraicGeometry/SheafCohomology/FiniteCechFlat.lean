/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.Algebra.FiniteFlatTwoTerm
import GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCechComplex

/-!
# Flat terms in finite Čech complexes

If the input has flat sections on a family of opens closed under intersection,
the corresponding finite Čech complex has flat terms. The proof uses finite
biproducts and does not assert flatness of cohomology.
-/

open CategoryTheory Limits HomologicalComplex TopologicalSpace Opposite

universe u v

namespace GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCech

open CochainComplex
set_option backward.isDefEq.respectTransparency false in
private lemma flat_map_biprod
    {A : Type*} [Category* A] [Preadditive A] [HasBinaryBiproducts A]
    {S : Type*} [CommRing S] (H : A ⥤ ModuleCat S) [H.Additive]
    (K L : A) [Module.Flat S (H.obj K)] [Module.Flat S (H.obj L)] :
    Module.Flat S (H.obj (K ⊞ L)) := by
  have : PreservesBinaryBiproducts H := preservesBinaryBiproducts_of_preservesBiproducts H
  have : Module.Flat S (H.obj K × H.obj L) := LinearMap.flat_prod_of_flat
  exact Module.Flat.of_linearEquiv
    ((H.mapBiprod K L) ≪≫ ModuleCat.biprodIsoProd (H.obj K) (H.obj L)).toLinearEquiv

set_option backward.isDefEq.respectTransparency false in
private lemma flat_map_cocone_X
    {A : Type*} [Category* A] [Preadditive A] [HasBinaryBiproducts A]
    {S : Type*} [CommRing S] (H : A ⥤ ModuleCat S) [H.Additive]
    {K L : CochainComplex A ℤ} (φ : K ⟶ L) (i : ℤ)
    [Module.Flat S (H.obj (K.X i))] [Module.Flat S (H.obj (L.X (i - 1)))] :
    Module.Flat S (H.obj ((mappingCocone φ).X i)) := by
  have : Module.Flat S (H.obj (K.X i ⊞ L.X (i - 1))) := flat_map_biprod H _ _
  let e : (mappingCocone φ).X i ≅ K.X i ⊞ L.X (i - 1) :=
    shiftFunctorObjXIso (mappingCone φ) (-1) i (i - 1) (by omega) ≪≫
      HomologicalComplex.homotopyCofiber.XIsoBiprod φ (i - 1) i (by
        change i - 1 + 1 = i
        omega)
  exact Module.Flat.of_linearEquiv (H.mapIso e).toLinearEquiv


variable {X : TopCat.{u}} {R : Type v} [CommRing R]
set_option backward.isDefEq.respectTransparency false in
/-- Termwise flatness on opens closed under intersection passes to the finite Čech complex. -/
lemma finiteCechData_flat_at (F : PresheafComplex X R)
    (P : Opens X → Prop) (hPinf : ∀ U V, P U → P V → P (U ⊓ V))
    (hF : ∀ W, P W → ∀ i : ℤ, Module.Flat R ((F.X i).obj (op W)))
    (U : List (Opens X)) (V : Opens X) (hU : ∀ W ∈ U, P (V ⊓ W)) :
    ∀ i : ℤ, Module.Flat R (((finiteCechData F U).complex.X i).obj (op V)) := by
  induction U generalizing V with
  | nil =>
      intro i
      have hz : IsZero (((finiteCechData F []).complex.X i).obj (op V)) := by
        exact Functor.map_isZero ((evaluation _ _).obj (op V))
          (by simpa [finiteCechData, HomologicalComplex.zero] using
            (isZero_zero (Presheaves X R)))
      have := ModuleCat.subsingleton_of_isZero hz
      infer_instance
  | cons U tail ih =>
      intro i
      let H := (evaluation (Opens X)ᵒᵖ (ModuleCat R)).obj (op V)
      let T := finiteCechData F tail
      let r := restrictionComplexFunctor (X := X) (R := R) U
      let φ : r.obj F ⊞ T.complex ⟶ r.obj T.complex :=
        biprod.desc (r.map T.augmentation) (-((restrictionComplexNatTrans U).app T.complex))
      have htail : ∀ W ∈ tail, P (V ⊓ W) := fun W hW => hU W (List.mem_cons_of_mem U hW)
      have htailU : ∀ W ∈ tail, P ((V ⊓ U) ⊓ W) := by
        intro W hW
        have hh := hPinf (V ⊓ U) (V ⊓ W) (hU U (by simp)) (htail W hW)
        simpa only [inf_assoc, inf_left_comm, inf_left_idem] using hh
      have hA : Module.Flat R (H.obj ((r.obj F).X i)) := hF (V ⊓ U) (hU U (by simp)) i
      have hB : Module.Flat R (H.obj (T.complex.X i)) := ih V htail i
      have hD : Module.Flat R (H.obj ((r.obj T.complex).X (i - 1))) :=
        ih (V ⊓ U) htailU (i - 1)
      have hAB : Module.Flat R (H.obj ((r.obj F ⊞ T.complex).X i)) := by
        have : Module.Flat R (H.obj ((r.obj F).X i ⊞ T.complex.X i)) :=
          flat_map_biprod H _ _
        exact Module.Flat.of_linearEquiv
          (H.mapIso (HomologicalComplex.biprodXIso (r.obj F) T.complex i)).toLinearEquiv
      exact flat_map_cocone_X H φ i


end GromovWitten.AlgebraicGeometry.SheafCohomology.FiniteCech
