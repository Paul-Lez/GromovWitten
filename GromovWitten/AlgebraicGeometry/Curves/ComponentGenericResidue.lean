/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/

import GromovWitten.AlgebraicGeometry.Curves.GeometricDualGraph

/-!
# Generic residue fields of reduced components

The function field of an integral scheme agrees with the residue field at the image of its
generic point under a morphism surjective on stalks. For the reduced irreducible components
of a prestable curve, that image is the generic point of the corresponding component.
-/

open CategoryTheory Limits AlgebraicGeometry Topology

namespace GromovWitten.AlgebraicGeometry.Curves

universe u

noncomputable section

variable {K : Type u} [Field K] {X : Scheme.{u}}

noncomputable def componentGenericPoint
    (f : X ⟶ Spec (.of K)) [PrestableFamily f] (C : Component X) :
    componentScheme f C :=
  @genericPoint (componentScheme f C) _ _ (componentScheme_isIrreducibleSpace f C)

theorem componentInclusion_genericPoint_closure
    (f : X ⟶ Spec (.of K)) [PrestableFamily f] (C : Component X) :
    closure ({componentInclusion f C (componentGenericPoint f C)} : Set X) =
      (C : Set X) := by
  let _ : IsNoetherian X := isNoetherian_of_quasiCompact f
  let := componentScheme_isIrreducibleSpace f C
  have hrange : Set.range (componentInclusion f C) = (C : Set X) := by
    change Set.range (X.irreducibleComponentIdeal C C.2).radical.subschemeι =
      (C : Set X)
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.support_radical]
    rfl
  have hg := (genericPoint_spec (componentScheme f C)).image
    (componentInclusion f C).continuous
  calc
    closure ({componentInclusion f C (componentGenericPoint f C)} : Set X) =
        closure ((componentInclusion f C) '' (Set.univ : Set (componentScheme f C))) := hg.def
    _ = closure (Set.range (componentInclusion f C)) := by rw [Set.image_univ]
    _ = closure (C : Set X) := by rw [hrange]
    _ = (C : Set X) := (isClosed_of_mem_irreducibleComponents _ C.2).closure_eq

variable {Cs : Scheme.{u}}

lemma residue_injective_of_isIntegral (Cs : Scheme.{u}) [IsIntegral Cs] :
    Function.Injective (Cs.residue (genericPoint Cs)) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  change RingHom.ker (IsLocalRing.residue (Cs.presheaf.stalk (genericPoint Cs))) = ⊥
  rw [IsLocalRing.ker_residue, IsLocalRing.maximalIdeal_eq_bot]

lemma residueFieldMap_surjective_of_surjectiveOnStalks
    {X : Scheme.{u}} (i : Cs ⟶ X) [SurjectiveOnStalks i] (η : Cs) :
    Function.Surjective (i.residueFieldMap η) := by
  intro z
  obtain ⟨s, hs⟩ := Cs.residue_surjective η z
  obtain ⟨t, ht⟩ := i.stalkMap_surjective η s
  refine ⟨X.residue (i η) t, ?_⟩
  have hnat := congrArg (fun q ↦ q t) (Scheme.residue_residueFieldMap i η)
  calc
    i.residueFieldMap η (X.residue (i η) t) = Cs.residue η (i.stalkMap η t) := by
      simpa using hnat
    _ = Cs.residue η s := by rw [ht]
    _ = z := hs

noncomputable def genericFunctionFieldResidueRingIso
    {X : Scheme.{u}} (i : Cs ⟶ X) [IsIntegral Cs] [SurjectiveOnStalks i] :
  (X.residueField (i (genericPoint Cs)) : Type u) ≃+*
      (Cs.functionField : Type u) := by
  let η : Cs := genericPoint Cs
  let er : (Cs.functionField : Type u) ≃+* (Cs.residueField η : Type u) :=
    RingEquiv.ofBijective (Cs.residue η).hom
      ⟨residue_injective_of_isIntegral Cs, Cs.residue_surjective η⟩
  let eq : (X.residueField (i η) : Type u) ≃+*
      (Cs.residueField η : Type u) :=
    RingEquiv.ofBijective (i.residueFieldMap η).hom
      ⟨RingHom.injective _, residueFieldMap_surjective_of_surjectiveOnStalks i η⟩
  exact eq.trans er.symm

noncomputable def genericFunctionFieldResidueSpecIso
    {X : Scheme.{u}} (i : Cs ⟶ X) [IsIntegral Cs] [SurjectiveOnStalks i] :
    Spec Cs.functionField ≅ Spec (X.residueField (i (genericPoint Cs))) :=
  Scheme.Spec.mapIso (genericFunctionFieldResidueRingIso i).toCommRingCatIso.op

lemma genericFunctionFieldResidueSpecIso_commutes
    {X : Scheme.{u}} (i : Cs ⟶ X) [IsIntegral Cs] [SurjectiveOnStalks i] :
    (genericFunctionFieldResidueSpecIso i).hom ≫
        X.fromSpecResidueField (i (genericPoint Cs)) =
      Cs.fromSpecStalk (genericPoint Cs) ≫ i := by
  have he :
      (genericFunctionFieldResidueRingIso i).toCommRingCatIso.hom ≫
          Cs.residue (genericPoint Cs) = i.residueFieldMap (genericPoint Cs) := by
    ext z
    let er : (Cs.functionField : Type u) ≃+* (Cs.residueField (genericPoint Cs) : Type u) :=
      RingEquiv.ofBijective (Cs.residue (genericPoint Cs)).hom
        ⟨residue_injective_of_isIntegral Cs, Cs.residue_surjective (genericPoint Cs)⟩
    let eq : (X.residueField (i (genericPoint Cs)) : Type u) ≃+*
        (Cs.residueField (genericPoint Cs) : Type u) :=
      RingEquiv.ofBijective (i.residueFieldMap (genericPoint Cs)).hom
        ⟨RingHom.injective _, residueFieldMap_surjective_of_surjectiveOnStalks i _⟩
    change er ((eq.trans er.symm) z) = eq z
    rw [RingEquiv.trans_apply, er.apply_symm_apply]
  have hstalk :
      X.residue (i (genericPoint Cs)) ≫
          (genericFunctionFieldResidueRingIso i).toCommRingCatIso.hom =
        i.stalkMap (genericPoint Cs) := by
    let : Mono (Cs.residue (genericPoint Cs)) :=
      ConcreteCategory.mono_of_injective _ (residue_injective_of_isIntegral Cs)
    apply (cancel_mono (Cs.residue (genericPoint Cs))).1
    rw [Category.assoc, he, Scheme.residue_residueFieldMap]
  change (Scheme.Spec.mapIso (genericFunctionFieldResidueRingIso i).toCommRingCatIso.op).hom ≫
    X.fromSpecResidueField (i (genericPoint Cs)) = _
  rw [Scheme.fromSpecResidueField]
  simp only [Functor.mapIso_hom, Iso.op_hom]
  rw [Scheme.Spec_map]
  change Spec.map (genericFunctionFieldResidueRingIso i).toCommRingCatIso.hom ≫
      Spec.map (X.residue (i (genericPoint Cs))) ≫ X.fromSpecStalk _ = _
  rw [← Spec.map_comp_assoc, hstalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

end
end GromovWitten.AlgebraicGeometry.Curves
