/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.CotangentComplex.PerfectDual
import Mathlib.RingTheory.Finiteness.Projective

/-!
# Perfect complexes with finite-projective representatives

The affine perfect-complex predicate in `PerfectComplex` uses bounded finite free complexes.  This
file records the genuine affine variant with bounded finite projective representatives.  A finite
projective module is given by the two module-theoretic properties `Module.Finite` and
`Module.Projective`; it is deliberately not identified with a globally free module.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TensorProduct

namespace GromovWitten.AlgebraicGeometry.CotangentComplex

namespace PerfectComplex

universe u

variable {R : Type u} [CommRing R]

/-! ## Finite projective modules -/

/-- A finite projective `R`-module object.  The two fields are the actual module-theoretic
conditions, rather than a supplied finiteness or freeness conclusion. -/
structure IsFiniteProjective (M : ModuleCat.{u} R) : Prop where
  finite : Module.Finite R M
  projective : Module.Projective R M

/-- Finite free modules are finite projective. -/
theorem IsFiniteFree.isFiniteProjective {M : ModuleCat.{u} R} (hM : IsFiniteFree M) :
    IsFiniteProjective M := by
  have := hM.free
  exact ⟨hM.finite, inferInstance⟩

/-- The zero module object is finite projective. -/
theorem isFiniteProjective_of_isZero {M : ModuleCat.{u} R} (h : IsZero M) :
    IsFiniteProjective M := by
  have hsub : Subsingleton M := ModuleCat.isZero_iff_subsingleton.mp h
  have := hsub
  have hfree : Module.Free R M := Module.Free.of_subsingleton R M
  have := hfree
  exact ⟨finite_of_subsingleton M, inferInstance⟩

namespace IsFiniteProjective

variable {M N : ModuleCat.{u} R}

/-- Finite projectivity is invariant under module isomorphism. -/
theorem of_iso (hM : IsFiniteProjective M) (e : M ≅ N) : IsFiniteProjective N := by
  have := hM.projective
  have := hM.finite
  exact ⟨Module.Finite.equiv e.toLinearEquiv, Module.Projective.of_equiv' e.toLinearEquiv⟩

/-- Binary biproducts of finite projectives are finite projective. -/
theorem biprod (hM : IsFiniteProjective M) (hN : IsFiniteProjective N) :
    IsFiniteProjective (M ⊞ N) := by
  have := hM.projective
  have := hN.projective
  have := hM.finite
  have := hN.finite
  let e : (M ⊞ N : ModuleCat.{u} R) ≃ₗ[R] (M × N) :=
    (ModuleCat.biprodIsoProd M N).toLinearEquiv
  exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv' e.symm⟩

/-- A direct summand of a finite projective module is finite projective.  Finiteness is proved
from the explicit splitting and the surjective retraction; projectivity is the corresponding
module-theoretic lifting theorem. -/
theorem of_split {P : ModuleCat.{u} R} (hP : IsFiniteProjective P)
    (i : M →ₗ[R] P) (p : P →ₗ[R] M) (hp : p.comp i = LinearMap.id) :
    IsFiniteProjective M := by
  have := hP.finite
  have := hP.projective
  refine ⟨Module.Finite.of_surjective p ?_, Module.Projective.of_split i p hp⟩
  intro m
  refine ⟨i m, ?_⟩
  change (p.comp i) m = m
  rw [hp, LinearMap.id_apply]

end IsFiniteProjective

/-! ## Scalar extension -/

section BaseChange

variable {S : Type u} [CommRing S] (f : R →+* S)

/-- Extension of scalars preserves finite projective module objects.  The proof exhibits the
extension as a retract of the scalar extension of a finite free module. -/
theorem IsFiniteProjective.extendScalars {M : ModuleCat.{u} R} (hM : IsFiniteProjective M) :
    IsFiniteProjective ((ModuleCat.extendScalars f).obj M) := by
  let _ : Algebra R S := f.toAlgebra
  have := hM.finite
  have := hM.projective
  obtain ⟨n, q, r, hq, hr, hqr⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  let iq := q.baseChange S
  let ir := r.baseChange S
  have hsplit : iq.comp ir = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hqr, LinearMap.baseChange_id]
  have hfreeR : IsFiniteFree (ModuleCat.of R (Fin n → R)) :=
    ⟨inferInstance, inferInstance⟩
  have hfree : IsFiniteProjective
      ((ModuleCat.extendScalars f).obj (ModuleCat.of R (Fin n → R))) :=
    (hfreeR.extendScalars f).isFiniteProjective
  change IsFiniteProjective (ModuleCat.of S (S ⊗[R] M))
  change IsFiniteProjective (ModuleCat.of S (S ⊗[R] (Fin n → R))) at hfree
  exact IsFiniteProjective.of_split hfree ir iq hsplit

end BaseChange

/-! ## Bounded finite-projective complexes -/

/-- A bounded complex whose terms are finite projective modules. -/
structure IsStrictlyProjective (K : CochainComplex (ModuleCat.{u} R) ℤ) : Prop where
  bounded : ∃ a b : ℤ, IsSupportedIn K a b
  finiteProjective : ∀ i : ℤ, IsFiniteProjective (K.X i)

/-- A bounded finite-free complex is bounded finite-projective. -/
theorem IsStrictlyPerfect.isStrictlyProjective
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsStrictlyPerfect K) :
    IsStrictlyProjective K where
  bounded := hK.bounded
  finiteProjective := fun i => (hK.finiteFree i).isFiniteProjective

namespace IsStrictlyProjective

variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

/-- Strict finite-projectivity transports along an isomorphism of complexes. -/
theorem of_iso (h : IsStrictlyProjective K) (e : K ≅ L) : IsStrictlyProjective L where
  bounded := by
    obtain ⟨a, b, hab⟩ := h.bounded
    exact ⟨a, b, hab.of_iso e⟩
  finiteProjective i := (h.finiteProjective i).of_iso ((HomologicalComplex.eval _ _ i).mapIso e)

/-- Shifts preserve strict finite-projectivity. -/
theorem shift (h : IsStrictlyProjective K) (n : ℤ) :
    IsStrictlyProjective
      ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) n).obj K) where
  bounded := by
    obtain ⟨a, b, hab⟩ := h.bounded
    exact ⟨a - n, b - n, fun i hi => hab (i + n) (by omega)⟩
  finiteProjective i := by
    rw [CochainComplex.shiftFunctor_obj_X']
    exact h.finiteProjective (i + n)

/-- Binary biproducts preserve strict finite-projectivity. -/
theorem biprod (hK : IsStrictlyProjective K) (hL : IsStrictlyProjective L) :
    IsStrictlyProjective (K ⊞ L) where
  bounded := by
    obtain ⟨a, b, hab⟩ := hK.bounded
    obtain ⟨a', b', hab'⟩ := hL.bounded
    refine ⟨min a a', max b b', fun i hi => ?_⟩
    refine IsZero.of_iso ?_ (HomologicalComplex.biprodXIso K L i)
    rw [biprod_isZero_iff]
    exact ⟨hab i (by omega), hab' i (by omega)⟩
  finiteProjective i :=
    ((hK.finiteProjective i).biprod (hL.finiteProjective i)).of_iso
      (HomologicalComplex.biprodXIso K L i).symm

end IsStrictlyProjective

/-- Mapping cones of maps between bounded finite-projective complexes are bounded
finite-projective. -/
theorem isStrictlyProjective_mappingCone {F G : CochainComplex (ModuleCat.{u} R) ℤ} (φ : F ⟶ G)
    (hF : IsStrictlyProjective F) (hG : IsStrictlyProjective G) :
    IsStrictlyProjective (CochainComplex.mappingCone φ) where
  bounded := by
    obtain ⟨a, b, hab⟩ := hF.bounded
    obtain ⟨a', b', hab'⟩ := hG.bounded
    refine ⟨min (a - 1) a', max (b - 1) b', fun i hi => ?_⟩
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨hab (i + 1) (by omega), hab' i (by omega)⟩
  finiteProjective i := by
    have := HomologicalComplex.HasHomotopyCofiber.hasBinaryBiproduct φ i (i + 1) rfl
    exact ((hF.finiteProjective (i + 1)).biprod (hG.finiteProjective i)).of_iso
      (HomologicalComplex.homotopyCofiber.XIsoBiprod φ i (i + 1) rfl).symm

section BaseChangeComplex

variable {S : Type u} [CommRing S] (f : R →+* S)

/-- Termwise scalar extension preserves strict finite-projectivity. -/
theorem IsStrictlyProjective.baseChange {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyProjective K) :
    IsStrictlyProjective (baseChange f K) where
  bounded := by
    obtain ⟨a, b, hab⟩ := hK.bounded
    exact ⟨a, b, fun i hi => by
      rw [baseChange_X]
      exact (ModuleCat.extendScalars f).map_isZero (hab i hi)⟩
  finiteProjective i := (hK.finiteProjective i).extendScalars f

end BaseChangeComplex

/-- A bounded finite-projective complex is K-projective. -/
theorem IsStrictlyProjective.isKProjective {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyProjective K) : K.IsKProjective := by
  obtain ⟨a, b, hab⟩ := hK.bounded
  have : K.IsStrictlyLE b := Modules.Derived.isStrictlyLE_of_isSupportedIn hab
  have hp : ∀ n, Projective (K.X n) := fun n => by
    have := (hK.finiteProjective n).projective
    exact ModuleCat.projective_of_categoryTheory_projective (K.X n)
  have : ∀ n, Projective (K.X n) := hp
  exact Modules.Derived.isKProjective_of_isStrictlyLE K b

/-! ## Derived objects represented by finite-projective complexes -/

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- A derived `R`-module is projective-perfect when it has an actual bounded finite-projective
complex representative. -/
def IsProjectivePerfect (E : DerivedCategory (ModuleCat.{u} R)) : Prop :=
  ∃ K : CochainComplex (ModuleCat.{u} R) ℤ,
    IsStrictlyProjective K ∧ Nonempty (DerivedCategory.Q.obj K ≅ E)

/-- A strict finite-projective complex gives a projective-perfect derived object. -/
theorem isProjectivePerfect_Q {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : IsStrictlyProjective K) : IsProjectivePerfect (DerivedCategory.Q.obj K) :=
  ⟨K, hK, ⟨Iso.refl _⟩⟩

/-- Every globally finite-free perfect object is projective-perfect. -/
theorem IsPerfect.isProjectivePerfect {E : DerivedCategory (ModuleCat.{u} R)}
    (hE : IsPerfect E) : IsProjectivePerfect E := by
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  exact ⟨K, hK.isStrictlyProjective, ⟨e⟩⟩

namespace IsProjectivePerfect

variable {E F : DerivedCategory (ModuleCat.{u} R)}

/-- Projective-perfectness transports along derived isomorphisms. -/
theorem of_iso (h : IsProjectivePerfect E) (e : E ≅ F) : IsProjectivePerfect F := by
  obtain ⟨K, hK, ⟨f⟩⟩ := h
  exact ⟨K, hK, ⟨f ≪≫ e⟩⟩

/-- Shifts preserve projective-perfectness. -/
theorem shift (h : IsProjectivePerfect E) (n : ℤ) : IsProjectivePerfect (E⟦n⟧) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := h
  refine ⟨(CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) n).obj K,
    hK.shift n, ⟨?_⟩⟩
  exact (DerivedCategory.Q.commShiftIso n).app K ≪≫
    (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} R)) n).mapIso e

/-- Binary biproducts preserve projective-perfectness. -/
theorem biprod (hE : IsProjectivePerfect E) (hF : IsProjectivePerfect F) :
    IsProjectivePerfect (E ⊞ F) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  obtain ⟨L, hL, ⟨f⟩⟩ := hF
  have : PreservesBinaryBiproducts (DerivedCategory.Q (C := ModuleCat.{u} R)) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  exact ⟨K ⊞ L, hK.biprod hL,
    ⟨Functor.mapBiprod DerivedCategory.Q K L ≪≫ biprod.mapIso e f⟩⟩

end IsProjectivePerfect

/-! ## Lifting and triangles -/

/-- A derived morphism out of a bounded finite-projective complex is represented by a chain map.
The proof uses the K-projectivity of the source, rather than a freeness assumption. -/
theorem exists_chainMap_of_projectiveDerivedMap
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsStrictlyProjective K)
    {L : CochainComplex (ModuleCat.{u} R) ℤ}
    (u : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :
    ∃ φ : K ⟶ L, DerivedCategory.Q.map φ = u := by
  obtain ⟨a, b, hab⟩ := hK.bounded
  have _ := IsStrictlyProjective.isKProjective hK
  have : K.IsStrictlyLE b := Modules.Derived.isStrictlyLE_of_isSupportedIn hab
  have : ∀ n, Projective (K.X n) := fun n => by
    have := (hK.finiteProjective n).projective
    exact ModuleCat.projective_of_categoryTheory_projective (K.X n)
  obtain ⟨γ, hγ⟩ :=
    (CochainComplex.IsKProjective.Qh_map_bijective K
      ((HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj L)).surjective
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.app K ≫ u ≫
        (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).inv.app L)
  obtain ⟨φ, rfl⟩ :=
    (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map_surjective γ
  refine ⟨φ, ?_⟩
  have hnat := (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).hom.naturality φ
  rw [Functor.comp_map, hγ] at hnat
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at hnat
  exact ((cancel_epi _).mp hnat).symm

/-- The third vertex of a distinguished triangle with two projective-perfect vertices is
projective-perfect, by lifting the first derived morphism to a chain map and taking its cone. -/
theorem exists_mappingCone_iso_of_projectivePerfect_distTriang
    (T : Triangle (DerivedCategory (ModuleCat.{u} R))) (hT : T ∈ distTriang _)
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsStrictlyProjective K)
    (e : DerivedCategory.Q.obj K ≅ T.obj₁) (_hL : IsStrictlyProjective L)
    (e' : DerivedCategory.Q.obj L ≅ T.obj₂) :
    ∃ φ : K ⟶ L,
      Nonempty (DerivedCategory.Q.obj (CochainComplex.mappingCone φ) ≅ T.obj₃) := by
  obtain ⟨φ, hφ⟩ := exists_chainMap_of_projectiveDerivedMap hK
    (e.hom ≫ T.mor₁ ≫ e'.inv)
  refine ⟨φ, ?_⟩
  have hT₁ : DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle φ) ∈
      distTriang (DerivedCategory (ModuleCat.{u} R)) :=
    DerivedCategory.mappingCone_triangle_distinguished φ
  have hcomm : DerivedCategory.Q.map φ ≫ e'.hom = e.hom ≫ T.mor₁ := by
    rw [hφ, Category.assoc, Category.assoc, e'.inv_hom_id, Category.comp_id]
  obtain ⟨c, hc₂, hc₃⟩ :=
    Pretriangulated.complete_distinguished_triangle_morphism _ _ hT₁ hT e.hom e'.hom hcomm
  have hiso : IsIso c := by
    refine Pretriangulated.isIso₃_of_isIso₁₂
      (Triangle.homMk _ _ e.hom e'.hom c hcomm hc₂ hc₃) hT₁ hT ?_ ?_
    · exact e.isIso_hom
    · exact e'.isIso_hom
  exact ⟨@asIso _ _ _ _ c hiso⟩

namespace IsProjectivePerfect

/-- Two-out-of-three, third vertex. -/
theorem of_distTriang₃ (T : Triangle (DerivedCategory (ModuleCat.{u} R)))
    (hT : T ∈ distTriang _) (h₁ : IsProjectivePerfect T.obj₁)
    (h₂ : IsProjectivePerfect T.obj₂) : IsProjectivePerfect T.obj₃ := by
  obtain ⟨K, hK, ⟨e⟩⟩ := h₁
  obtain ⟨L, hL, ⟨e'⟩⟩ := h₂
  obtain ⟨φ, ⟨f⟩⟩ := exists_mappingCone_iso_of_projectivePerfect_distTriang T hT hK e hL e'
  exact ⟨CochainComplex.mappingCone φ, isStrictlyProjective_mappingCone φ hK hL, ⟨f⟩⟩

/-- Two-out-of-three, second vertex. -/
theorem of_distTriang₂ (T : Triangle (DerivedCategory (ModuleCat.{u} R)))
    (hT : T ∈ distTriang _) (h₁ : IsProjectivePerfect T.obj₁)
    (h₃ : IsProjectivePerfect T.obj₃) : IsProjectivePerfect T.obj₂ :=
  of_distTriang₃ T.invRotate (Pretriangulated.inv_rot_of_distTriang _ hT)
    (h₃.shift (-1)) h₁

/-- Two-out-of-three, first vertex. -/
theorem of_distTriang₁ (T : Triangle (DerivedCategory (ModuleCat.{u} R)))
    (hT : T ∈ distTriang _) (h₂ : IsProjectivePerfect T.obj₂)
    (h₃ : IsProjectivePerfect T.obj₃) : IsProjectivePerfect T.obj₁ := by
  have h := of_distTriang₃ T.rotate (Pretriangulated.rot_of_distTriang _ hT) h₂ h₃
  exact (h.shift (-1)).of_iso
    ((shiftFunctorCompIsoId (DerivedCategory (ModuleCat.{u} R)) 1 (-1) (by omega)).app T.obj₁)

end IsProjectivePerfect

end Derived

end PerfectComplex

end GromovWitten.AlgebraicGeometry.CotangentComplex
