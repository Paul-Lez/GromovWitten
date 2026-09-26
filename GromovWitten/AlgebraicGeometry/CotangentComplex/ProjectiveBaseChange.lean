/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import GromovWitten.AlgebraicGeometry.CotangentComplex.ProjectivePerfect
import GromovWitten.AlgebraicGeometry.CotangentComplex.PerfectDualInvariance

/-!
# Derived base change of projective-perfect complexes

Termwise extension of scalars is a derived operation on bounded finite-projective complexes.  The
point of this file is to make that statement independent of a chosen representative: a derived
isomorphism between two such representatives is represented by a homotopy equivalence, and every
additive scalar-extension functor carries that equivalence to a homotopy equivalence.

There is no base-change functor on the entire derived category here.  The construction below is
therefore deliberately indexed by a proof of `IsProjectivePerfect`; its comparison theorem is the
derived scalar-extension statement that is needed by downstream affine constructions.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace GromovWitten.AlgebraicGeometry.CotangentComplex

namespace PerfectComplex

universe u

variable {R : Type u} [CommRing R]

section ProjectiveHomotopy

attribute [local instance] HasDerivedCategory.standard

variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

/-! ## Quasi-isomorphisms between projective representatives -/

/-- A quasi-isomorphism between bounded finite-projective complexes is a homotopy equivalence.

The boundedness and projectivity hypotheses are exactly what is needed for the K-projective
criterion; no freeness or flatness assumption is used. -/
theorem homotopyEquivalences_of_quasiIso_projective
    (hK : IsStrictlyProjective K) (hL : IsStrictlyProjective L)
    (φ : K ⟶ L) (hφ : QuasiIso φ) :
    HomologicalComplex.homotopyEquivalences (ModuleCat.{u} R) (ComplexShape.up ℤ) φ := by
  have _ := hK.isKProjective
  have _ := hL.isKProjective
  exact (CochainComplex.IsKProjective.quasiIso_iff φ).1 hφ

/-- Every derived isomorphism between bounded finite-projective representatives is induced by a
homotopy equivalence. -/
theorem exists_homotopyEquiv_of_projectiveDerivedIso
    (hK : IsStrictlyProjective K) (hL : IsStrictlyProjective L)
    (e : DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj L) :
    ∃ f : HomotopyEquiv K L, DerivedCategory.Q.map f.hom = e.hom := by
  obtain ⟨φ, hφ⟩ := exists_chainMap_of_projectiveDerivedMap hK e.hom
  have hiso : IsIso (DerivedCategory.Q.map φ) := by
    rw [hφ]
    exact e.isIso_hom
  obtain ⟨f, hf⟩ := homotopyEquivalences_of_quasiIso_projective hK hL φ
    ((DerivedCategory.isIso_Q_map_iff_quasiIso _ φ).1 hiso)
  exact ⟨f, by rw [hf, hφ]⟩

end ProjectiveHomotopy

section BaseChange

attribute [local instance] HasDerivedCategory.standard

variable {S : Type u} [CommRing S] (f : R →+* S)

/-! ## A representative-indexed derived scalar extension -/

/-- The representative selected from a proof of projective-perfectness.  This is only a choice of
representative; all comparison theorems below show that the resulting derived object is invariant
under replacing it by any other projective representative. -/
noncomputable def IsProjectivePerfect.rep {E : DerivedCategory (ModuleCat.{u} R)}
    (hE : IsProjectivePerfect E) : CochainComplex (ModuleCat.{u} R) ℤ :=
  hE.choose

theorem IsProjectivePerfect.rep_isStrictlyProjective
    {E : DerivedCategory (ModuleCat.{u} R)} (hE : IsProjectivePerfect E) :
    IsStrictlyProjective (hE.rep) :=
  hE.choose_spec.1

/-- The derived isomorphism carried by the selected representative. -/
noncomputable def IsProjectivePerfect.repIso
    {E : DerivedCategory (ModuleCat.{u} R)} (hE : IsProjectivePerfect E) :
    DerivedCategory.Q.obj hE.rep ≅ E :=
  Classical.choice hE.choose_spec.2

/-- Derived scalar extension of a projective-perfect object, represented by extending scalars on
the selected bounded finite-projective complex. -/
noncomputable def IsProjectivePerfect.derivedBaseChange
    {E : DerivedCategory (ModuleCat.{u} R)} (hE : IsProjectivePerfect E) :
    DerivedCategory (ModuleCat.{u} S) :=
  DerivedCategory.Q.obj ((Modules.Derived.baseChangeFunctor f).obj hE.rep)

theorem IsProjectivePerfect.derivedBaseChange_isProjectivePerfect
    {E : DerivedCategory (ModuleCat.{u} R)} (hE : IsProjectivePerfect E) :
    IsProjectivePerfect (R := S) (IsProjectivePerfect.derivedBaseChange f hE) := by
  exact isProjectivePerfect_Q ((hE.rep_isStrictlyProjective).baseChange f)

/-- Comparison with any other bounded finite-projective representative of the same derived object.
The comparison is the image of an actual homotopy equivalence after scalar extension. -/
noncomputable def IsProjectivePerfect.derivedBaseChangeComparison
    {E : DerivedCategory (ModuleCat.{u} R)} (hE : IsProjectivePerfect E)
    {L : CochainComplex (ModuleCat.{u} R) ℤ} (hL : IsStrictlyProjective L)
    (e : DerivedCategory.Q.obj L ≅ E) :
    hE.derivedBaseChange f ≅
      DerivedCategory.Q.obj ((Modules.Derived.baseChangeFunctor f).obj L) := by
  let eKL : DerivedCategory.Q.obj hE.rep ≅ DerivedCategory.Q.obj L :=
    hE.repIso ≪≫ e.symm
  let hKL : HomotopyEquiv hE.rep L :=
    (exists_homotopyEquiv_of_projectiveDerivedIso
      hE.rep_isStrictlyProjective hL eKL).choose
  have hbase : HomologicalComplex.homotopyEquivalences (ModuleCat.{u} S) (ComplexShape.up ℤ)
      ((Modules.Derived.baseChangeFunctor f).map hKL.hom) := by
    exact (Functor.mapHomotopyEquiv (ModuleCat.extendScalars f) hKL).homotopyEquivalences_hom
  have hq : QuasiIso ((Modules.Derived.baseChangeFunctor f).map hKL.hom) :=
    homotopyEquivalences_le_quasiIso (ModuleCat.{u} S) (ComplexShape.up ℤ) _ hbase
  have hi : IsIso (DerivedCategory.Q.map
      ((Modules.Derived.baseChangeFunctor f).map hKL.hom)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hq
  exact @asIso _ _ _ _ (DerivedCategory.Q.map
    ((Modules.Derived.baseChangeFunctor f).map hKL.hom)) hi

/-- The comparison specialized to the selected representative and its selected derived
isomorphism. -/
noncomputable def IsProjectivePerfect.derivedBaseChangeComparison_rep
    {E : DerivedCategory (ModuleCat.{u} R)} (hE : IsProjectivePerfect E)
    : hE.derivedBaseChange f ≅
      DerivedCategory.Q.obj ((Modules.Derived.baseChangeFunctor f).obj hE.rep) := by
  exact hE.derivedBaseChangeComparison f hE.rep_isStrictlyProjective hE.repIso

/-- The identity scalar extension of a projective-perfect object is derived-isomorphic to the
original object.  The first factor is the termwise identity comparison and the second is the
chosen representative isomorphism. -/
noncomputable def IsProjectivePerfect.derivedBaseChangeIdIso
    {E : DerivedCategory (ModuleCat.{u} R)} (hE : IsProjectivePerfect E) :
    IsProjectivePerfect.derivedBaseChange (RingHom.id R) hE ≅ E := by
  let hrep : IsIso (DerivedCategory.Q.map
      ((Modules.Derived.baseChangeIdIso R).hom.app hE.rep)) := by infer_instance
  exact @asIso _ _ _ _ (DerivedCategory.Q.map
      ((Modules.Derived.baseChangeIdIso R).hom.app hE.rep)) hrep ≪≫ hE.repIso

section Composition

variable {T : Type u} [CommRing T]

/-- Comparison of iterated and direct scalar extension.  The middle comparison handles the
possibly different representative selected for the once-base-changed object; the final factor is
the actual chain-level comparison `baseChangeComp'`. -/
noncomputable def IsProjectivePerfect.derivedBaseChangeCompIso
    {E : DerivedCategory (ModuleCat.{u} R)} (hE : IsProjectivePerfect E)
    (g : S →+* T) (gf : R →+* T) (hgf : gf = g.comp f) :
    IsProjectivePerfect.derivedBaseChange g
        (IsProjectivePerfect.derivedBaseChange_isProjectivePerfect f hE) ≅
      IsProjectivePerfect.derivedBaseChange gf hE := by
  let hF : IsProjectivePerfect (R := S)
      (IsProjectivePerfect.derivedBaseChange f hE) :=
    IsProjectivePerfect.derivedBaseChange_isProjectivePerfect f hE
  let hL : IsStrictlyProjective
      ((Modules.Derived.baseChangeFunctor f).obj hE.rep) :=
    hE.rep_isStrictlyProjective.baseChange f
  let e₁ := hF.derivedBaseChangeComparison g hL (Iso.refl _)
  let e₂ := hE.derivedBaseChangeComparison gf hE.rep_isStrictlyProjective hE.repIso
  let ecomp :
      DerivedCategory.Q.obj ((Modules.Derived.baseChangeFunctor g).obj
        ((Modules.Derived.baseChangeFunctor f).obj hE.rep)) ≅
        DerivedCategory.Q.obj ((Modules.Derived.baseChangeFunctor gf).obj hE.rep) := by
    let hcomp : IsIso (DerivedCategory.Q.map
        ((Modules.Derived.baseChangeComp' f g gf hgf).hom.app hE.rep)) := by
      infer_instance
    exact @asIso _ _ _ _ (DerivedCategory.Q.map
      ((Modules.Derived.baseChangeComp' f g gf hgf).hom.app hE.rep)) hcomp
  exact e₁ ≪≫ ecomp ≪≫ e₂.symm

end Composition

end BaseChange

end PerfectComplex

end GromovWitten.AlgebraicGeometry.CotangentComplex
