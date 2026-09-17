/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/

import GromovWitten.AlgebraicGeometry.Modules.Stack
import GromovWitten.AlgebraicGeometry.CotangentComplex.PerfectComplex
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.Embedding.TruncGEHomology
import Mathlib.Algebra.Homology.Embedding.TruncLEHomology

/-!
# Derived module operations

This file assembles the derived-category operations on the module categories that the
repository actually constructs: sheaves of modules on a ringed site (`Sites/Stack.lean`,
`Modules/Stack.lean`) and `ModuleCat R`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace GromovWitten.AlgebraicGeometry.Modules

namespace Derived

universe w v u

/-! ## Cohomology, truncation and `Ext` in a derived category -/

section Abelian

variable (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- The `n`-th cohomology functor of the derived category, as provided by Mathlib. -/
noncomputable abbrev cohomologyFunctor (n : ℤ) : DerivedCategory A ⥤ A :=
  DerivedCategory.homologyFunctor A n

/-- Cohomology of the image of a cochain complex is the cohomology of the complex. -/
noncomputable abbrev cohomologyFunctorFactors (n : ℤ) :
    DerivedCategory.Q ⋙ cohomologyFunctor A n ≅
      HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) n :=
  DerivedCategory.homologyFunctorFactors A n

variable {A}

/-- Cohomology of a shift: `Hᵃ(E⟦n⟧) ≅ Hⁿ⁺ᵃ(E)`, as a natural isomorphism. -/
noncomputable def cohomologyShiftIso (n a a' : ℤ) (h : n + a = a') :
    CategoryTheory.shiftFunctor (DerivedCategory A) n ⋙ cohomologyFunctor A a ≅
      cohomologyFunctor A a' :=
  (DerivedCategory.homologyFunctor A 0).shiftIso n a a' h

/-- Cohomology of a shift, evaluated on an object. -/
noncomputable def cohomologyObjShiftIso (E : DerivedCategory A) (n a a' : ℤ) (h : n + a = a') :
    (cohomologyFunctor A a).obj (E⟦n⟧) ≅ (cohomologyFunctor A a').obj E :=
  (cohomologyShiftIso n a a' h).app E

/-- The shift comparison of cohomology is compatible with the identity shift. -/
theorem cohomologyShiftIso_zero (a : ℤ) :
    cohomologyShiftIso (A := A) 0 a a (zero_add a) =
      Functor.isoWhiskerRight (CategoryTheory.shiftFunctorZero (DerivedCategory A) ℤ)
        (cohomologyFunctor A a) ≪≫ (cohomologyFunctor A a).leftUnitor :=
  (DerivedCategory.homologyFunctor A 0).shiftIso_zero a

/-- The shift comparison of cohomology is compatible with composition of shifts. -/
theorem cohomologyShiftIso_add (n m a a' a'' : ℤ) (ha' : n + a = a') (ha'' : m + a' = a'') :
    cohomologyShiftIso (A := A) (m + n) a a'' (by lia) =
      Functor.isoWhiskerRight (CategoryTheory.shiftFunctorAdd (DerivedCategory A) m n)
          (cohomologyFunctor A a) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (cohomologyShiftIso n a a' ha') ≪≫
        cohomologyShiftIso m a' a'' ha'' :=
  (DerivedCategory.homologyFunctor A 0).shiftIso_add n m a a' a'' ha' ha''

variable (A)

/-- The canonical truncation functor `τ≤n` on cochain complexes. -/
noncomputable abbrev truncLEFunctor (n : ℤ) : CochainComplex A ℤ ⥤ CochainComplex A ℤ :=
  (ComplexShape.embeddingUpIntLE n).truncLEFunctor A

/-- The canonical truncation functor `τ≥n` on cochain complexes. -/
noncomputable abbrev truncGEFunctor (n : ℤ) : CochainComplex A ℤ ⥤ CochainComplex A ℤ :=
  (ComplexShape.embeddingUpIntGE n).truncGEFunctor A

variable {A}

/-- The short exact sequence `τ≤n K ⟶ K ⟶ K/τ≤n K` of cochain complexes. -/
noncomputable abbrev truncLEShortComplex (K : CochainComplex A ℤ) (n : ℤ) :
    ShortComplex (CochainComplex A ℤ) :=
  K.shortComplexTruncLE n

omit [HasDerivedCategory.{w} A] in
/-- The canonical truncation short complex is short exact. -/
theorem truncLEShortComplex_shortExact (K : CochainComplex A ℤ) (n : ℤ) :
    (truncLEShortComplex K n).ShortExact :=
  K.shortComplexTruncLE_shortExact n

/-- The truncation triangle `τ≤n K ⟶ K ⟶ K/τ≤n K ⟶ (τ≤n K)⟦1⟧` in the derived category. -/
noncomputable abbrev truncLETriangle (K : CochainComplex A ℤ) (n : ℤ) :
    Triangle (DerivedCategory A) :=
  DerivedCategory.triangleOfSES (truncLEShortComplex_shortExact K n)

/-- The truncation triangle is distinguished. -/
theorem truncLETriangle_distinguished (K : CochainComplex A ℤ) (n : ℤ) :
    truncLETriangle K n ∈ distTriang (DerivedCategory A) :=
  DerivedCategory.triangleOfSES_distinguished (truncLEShortComplex_shortExact K n)

omit [HasDerivedCategory.{w} A] in
/-- The truncation `τ≤n K ⟶ K` is a quasi-isomorphism in degrees `≤ n`. -/
theorem quasiIsoAt_ιTruncLE (K : CochainComplex A ℤ) (n q : ℤ) (hq : q ≤ n) :
    QuasiIsoAt (K.ιTruncLE n) q :=
  K.quasiIsoAt_ιTruncLE n q hq

omit [HasDerivedCategory.{w} A] in
/-- The truncation `K ⟶ τ≥n K` is a quasi-isomorphism in degrees `≥ n`. -/
theorem quasiIsoAt_πTruncGE (K : CochainComplex A ℤ) (n q : ℤ) (hq : n ≤ q) :
    QuasiIsoAt (K.πTruncGE n) q :=
  K.quasiIsoAt_πTruncGE n q hq

/-- The third term of the truncation triangle is canonically the truncation `τ≥n₁ K` in the
derived category, where `n₁ = n₀ + 1`. -/
noncomputable def truncLEX₃IsoTruncGE (K : CochainComplex A ℤ) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    DerivedCategory.Q.obj (truncLEShortComplex K n₀).X₃ ≅
      DerivedCategory.Q.obj (K.truncGE n₁) :=
  asIso (DerivedCategory.Q.map (K.shortComplexTruncLEX₃ToTruncGE n₀ n₁ h))

/-- The canonical truncation triangle `τ≤n₀ K ⟶ K ⟶ τ≥n₁ K ⟶ (τ≤n₀ K)⟦1⟧`. -/
noncomputable abbrev truncTriangle (K : CochainComplex A ℤ) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    Triangle (DerivedCategory A) :=
  Triangle.mk (truncLETriangle K n₀).mor₁
    ((truncLETriangle K n₀).mor₂ ≫ (truncLEX₃IsoTruncGE K n₀ n₁ h).hom)
    ((truncLEX₃IsoTruncGE K n₀ n₁ h).inv ≫ (truncLETriangle K n₀).mor₃)

/-- The first map of the canonical truncation triangle is `τ≤n₀ K ⟶ K`. -/
theorem truncTriangle_mor₁ (K : CochainComplex A ℤ) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (truncTriangle K n₀ n₁ h).mor₁ = DerivedCategory.Q.map (K.ιTruncLE n₀) :=
  rfl

/-- The second map of the canonical truncation triangle is `K ⟶ τ≥n₁ K`. -/
theorem truncTriangle_mor₂ (K : CochainComplex A ℤ) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (truncTriangle K n₀ n₁ h).mor₂ = DerivedCategory.Q.map (K.πTruncGE n₁) := by
  change DerivedCategory.Q.map (K.shortComplexTruncLE n₀).g ≫
    DerivedCategory.Q.map (K.shortComplexTruncLEX₃ToTruncGE n₀ n₁ h) = _
  rw [← Functor.map_comp]
  exact congrArg _ (K.g_shortComplexTruncLEX₃ToTruncGE n₀ n₁ h)

/-- The canonical truncation triangle is isomorphic to the truncation triangle attached to the
short exact truncation sequence. -/
noncomputable def truncTriangleIso (K : CochainComplex A ℤ) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    truncLETriangle K n₀ ≅ truncTriangle K n₀ n₁ h :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (truncLEX₃IsoTruncGE K n₀ n₁ h)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.id_comp _).symm)
    (by
      change DerivedCategory.triangleOfSESδ (truncLEShortComplex_shortExact K n₀) ≫
          (CategoryTheory.shiftFunctor (DerivedCategory A) (1 : ℤ)).map
            (𝟙 (DerivedCategory.Q.obj (K.shortComplexTruncLE n₀).X₁)) =
        (truncLEX₃IsoTruncGE K n₀ n₁ h).hom ≫ (truncLEX₃IsoTruncGE K n₀ n₁ h).inv ≫
          DerivedCategory.triangleOfSESδ (truncLEShortComplex_shortExact K n₀)
      rw [CategoryTheory.Functor.map_id, Category.comp_id, Iso.hom_inv_id_assoc])

/-- The canonical truncation triangle is distinguished. -/
theorem truncTriangle_distinguished (K : CochainComplex A ℤ) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    truncTriangle K n₀ n₁ h ∈ distTriang (DerivedCategory A) :=
  isomorphic_distinguished _ (truncLETriangle_distinguished K n₀) _
    (truncTriangleIso K n₀ n₁ h).symm

variable (A)

/-- `Ext` groups of the abelian category, as provided by Mathlib, are available as soon as a
derived category with `w`-small morphisms has been chosen. -/
theorem hasExt : HasExt.{w} A :=
  hasExt_of_hasDerivedCategory A

end Abelian

/-! ## The derived category of module sheaves on a ringed site -/

section StackSite

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C] [UnivLE.{max u v, w}]
  (S : Sites.RingedSite.{w} C)
  [HasSheafify S.topology AddCommGrpCat.{w}]
  [S.topology.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Module sheaves on a ringed site form an abelian category.  This is Mathlib's abelian
structure on `SheafOfModules`, obtained from the sheafification adjunction; it is available
exactly under the two sheafification hypotheses carried by this section. -/
noncomputable abbrev modulesAbelian : Abelian S.Modules :=
  inferInstance

/-- The derived category of module sheaves on a ringed site, using Mathlib's standard choice
of a localization of cochain complexes at the quasi-isomorphisms. -/
noncomputable abbrev ModulesDerivedCategory := DerivedCategory S.Modules

/-- The `n`-th cohomology functor on the derived category of module sheaves. -/
noncomputable abbrev modulesCohomologyFunctor (n : ℤ) :
    ModulesDerivedCategory S ⥤ S.Modules :=
  cohomologyFunctor S.Modules n

/-- The canonical truncation functor `τ≤n` on complexes of module sheaves. -/
noncomputable abbrev modulesTruncLEFunctor (n : ℤ) :
    CochainComplex S.Modules ℤ ⥤ CochainComplex S.Modules ℤ :=
  truncLEFunctor S.Modules n

/-- The canonical truncation functor `τ≥n` on complexes of module sheaves. -/
noncomputable abbrev modulesTruncGEFunctor (n : ℤ) :
    CochainComplex S.Modules ℤ ⥤ CochainComplex S.Modules ℤ :=
  truncGEFunctor S.Modules n

/-- The canonical truncation triangle of a complex of module sheaves is distinguished. -/
theorem modules_truncTriangle_distinguished (K : CochainComplex S.Modules ℤ) (n₀ n₁ : ℤ)
    (h : n₀ + 1 = n₁) :
    truncTriangle K n₀ n₁ h ∈ distTriang (ModulesDerivedCategory S) :=
  truncTriangle_distinguished K n₀ n₁ h

/-- `Ext` groups of module sheaves on a ringed site exist in Mathlib's sense. -/
theorem modules_hasExt : HasExt.{max u v (w + 1)} S.Modules :=
  hasExt _

end StackSite

/-! ## The derived category of modules over a ring -/

section ModuleCatDerived

attribute [local instance] HasDerivedCategory.standard

variable (R : Type u) [CommRing R]

/-- The derived category of `R`-modules. -/
noncomputable abbrev ModuleDerivedCategory := DerivedCategory (ModuleCat.{u} R)

/-- The `n`-th cohomology functor on the derived category of `R`-modules. -/
noncomputable abbrev moduleCohomologyFunctor (n : ℤ) :
    ModuleDerivedCategory R ⥤ ModuleCat.{u} R :=
  cohomologyFunctor (ModuleCat.{u} R) n

/-- `Ext` groups of `R`-modules exist in Mathlib's sense. -/
theorem module_hasExt : HasExt.{u + 1} (ModuleCat.{u} R) :=
  hasExt _

end ModuleCatDerived

/-! ## Derived base change along a ring homomorphism -/

section BaseChange

open CotangentComplex.PerfectComplex

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R] {S : Type u} [CommRing S] (f : R →+* S)

/-- Termwise base change of cochain complexes along a ring homomorphism.  On objects this is
the complex `CotangentComplex.PerfectComplex.baseChange f`. -/
noncomputable abbrev baseChangeFunctor :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} S) ℤ :=
  (ModuleCat.extendScalars f).mapHomologicalComplex _

/-- Termwise base change of complexes agrees with the object-level base change already
constructed for perfect complexes. -/
theorem baseChangeFunctor_obj (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (baseChangeFunctor f).obj K = baseChange f K :=
  rfl

/-- Base change preserves homotopies between maps of complexes. -/
noncomputable def baseChangeHomotopy {K L : CochainComplex (ModuleCat.{u} R) ℤ} {a b : K ⟶ L}
    (H : Homotopy a b) :
    Homotopy ((baseChangeFunctor f).map a) ((baseChangeFunctor f).map b) :=
  (ModuleCat.extendScalars f).mapHomotopy H

/-- Base change preserves homotopy equivalences of complexes. -/
noncomputable def baseChangeHomotopyEquiv {K L : CochainComplex (ModuleCat.{u} R) ℤ}
    (e : HomotopyEquiv K L) :
    HomotopyEquiv ((baseChangeFunctor f).obj K) ((baseChangeFunctor f).obj L) :=
  (ModuleCat.extendScalars f).mapHomotopyEquiv e

omit [CommRing S] in
/-- A finite free module object is a projective object of `ModuleCat R`. -/
theorem projective_of_isFiniteFree {M : ModuleCat.{u} R} (h : IsFiniteFree M) :
    Projective M := by
  have := h.free
  have : Module.Projective R M := inferInstance
  exact ModuleCat.projective_of_categoryTheory_projective M

omit [CommRing S] in
/-- A complex supported in degrees `≤ b` is strictly `≤ b` in Mathlib's sense. -/
theorem isStrictlyLE_of_isSupportedIn {K : CochainComplex (ModuleCat.{u} R) ℤ} {a b : ℤ}
    (h : IsSupportedIn K a b) : K.IsStrictlyLE b :=
  (CochainComplex.isStrictlyLE_iff K b).2 fun i hi => h i (Or.inr hi)

omit [CommRing S] in
/-- A bounded-above complex of projective modules is K-projective. -/
theorem isKProjective_of_isStrictlyLE (K : CochainComplex (ModuleCat.{u} R) ℤ) (d : ℤ)
    [K.IsStrictlyLE d] [∀ n, Projective (K.X n)] : K.IsKProjective :=
  CochainComplex.isKProjective_of_projective K d

omit [CommRing S] in
/-- A strictly perfect complex supported in degrees `≤ d` is K-projective. -/
theorem isKProjective_of_isStrictlyPerfect {K : CochainComplex (ModuleCat.{u} R) ℤ} {a b : ℤ}
    (hK : IsStrictlyPerfect K) (hs : IsSupportedIn K a b) : K.IsKProjective := by
  have : K.IsStrictlyLE b := isStrictlyLE_of_isSupportedIn hs
  have : ∀ n, Projective (K.X n) := fun n => projective_of_isFiniteFree (hK.finiteFree n)
  exact isKProjective_of_isStrictlyLE K b

/-- Homotopy invariance of termwise base change: a quasi-isomorphism between bounded-above
complexes of projective modules becomes a quasi-isomorphism after base change.  This is exactly
the statement that derived base change is well defined on such complexes. -/
theorem quasiIso_baseChangeFunctor_map {K L : CochainComplex (ModuleCat.{u} R) ℤ} (d : ℤ)
    [K.IsStrictlyLE d] [L.IsStrictlyLE d]
    [∀ n, Projective (K.X n)] [∀ n, Projective (L.X n)]
    (φ : K ⟶ L) [QuasiIso φ] : QuasiIso ((baseChangeFunctor f).map φ) := by
  have hK : K.IsKProjective := isKProjective_of_isStrictlyLE K d
  have hL : L.IsKProjective := isKProjective_of_isStrictlyLE L d
  obtain ⟨e, he⟩ := (CochainComplex.IsKProjective.quasiIso_iff φ).1 inferInstance
  have hmem : HomologicalComplex.homotopyEquivalences (ModuleCat.{u} S) (ComplexShape.up ℤ)
      ((baseChangeFunctor f).map φ) := by
    refine ⟨baseChangeHomotopyEquiv f e, ?_⟩
    rw [← he]
    rfl
  have := homotopyEquivalences_le_quasiIso (ModuleCat.{u} S) (ComplexShape.up ℤ) _ hmem
  rwa [HomologicalComplex.mem_quasiIso_iff] at this

/-- Derived base change is well defined on quasi-isomorphisms: quasi-isomorphic bounded-above
complexes of projective modules have canonically isomorphic base changes in the derived
category of `S`-modules. -/
noncomputable def baseChangeDerivedIso {K L : CochainComplex (ModuleCat.{u} R) ℤ} (d : ℤ)
    [K.IsStrictlyLE d] [L.IsStrictlyLE d]
    [∀ n, Projective (K.X n)] [∀ n, Projective (L.X n)]
    (φ : K ⟶ L) [QuasiIso φ] :
    DerivedCategory.Q.obj ((baseChangeFunctor f).obj K) ≅
      DerivedCategory.Q.obj ((baseChangeFunctor f).obj L) :=
  have := quasiIso_baseChangeFunctor_map f d φ
  asIso (DerivedCategory.Q.map ((baseChangeFunctor f).map φ))

end BaseChange

/-! ## Pseudofunctoriality of base change -/

section Pseudofunctor

open scoped ChangeOfRings

variable {R : Type u} [CommRing R] {S : Type u} [CommRing S] {T : Type u} [CommRing T]
  {U : Type u} [CommRing U]

/-- Extension of scalars along the identity ring homomorphism is the identity functor.  The
comparison is the mate, under the extension/restriction adjunctions, of Mathlib's identity
comparison for restriction of scalars; it is not extra data. -/
noncomputable def extendScalarsIdIso (R : Type u) [CommRing R] :
    ModuleCat.extendScalars.{u} (RingHom.id R) ≅ 𝟭 (ModuleCat.{u} R) :=
  ((conjugateIsoEquiv (ModuleCat.extendRestrictScalarsAdj (RingHom.id R))
    (Adjunction.id (C := ModuleCat.{u} R))).symm (ModuleCat.restrictScalarsId R)).symm

/-- Extension of scalars along a composite ring homomorphism is the composite of the extensions.
The comparison is the mate of Mathlib's composition comparison for restriction of scalars. -/
noncomputable def extendScalarsComp' (f : R →+* S) (g : S →+* T) (gf : R →+* T)
    (hgf : gf = g.comp f) :
    ModuleCat.extendScalars.{u} f ⋙ ModuleCat.extendScalars.{u} g ≅
      ModuleCat.extendScalars.{u} gf :=
  (conjugateIsoEquiv (ModuleCat.extendRestrictScalarsAdj gf)
      ((ModuleCat.extendRestrictScalarsAdj f).comp
        (ModuleCat.extendRestrictScalarsAdj g))).symm
    (ModuleCat.restrictScalarsComp' f g gf hgf)

/-- The identity comparison of extension of scalars sends `r ⊗ m` to `r • m`. -/
@[simp] theorem extendScalarsIdIso_hom_app_tmul (M : ModuleCat.{u} R) (r : R) (m : M) :
    (extendScalarsIdIso R).hom.app M (r ⊗ₜ[R, RingHom.id R] m) = r • m := by
  simp only [extendScalarsIdIso, conjugateIsoEquiv, conjugateEquiv, mateEquiv, Adjunction.id,
    Iso.symm_hom]
  rfl

/-- The composition comparison of extension of scalars sends `t ⊗ (s ⊗ m)` to `(t * g s) ⊗ m`. -/
@[simp] theorem extendScalarsComp'_hom_app_tmul (f : R →+* S) (g : S →+* T) (gf : R →+* T)
    (hgf : gf = g.comp f) (M : ModuleCat.{u} R) (t : T) (s : S) (m : M) :
    (extendScalarsComp' f g gf hgf).hom.app M (t ⊗ₜ[S, g] (s ⊗ₜ[R, f] m)) =
      (t * g s) ⊗ₜ[R, gf] m := by
  change ((t * (g s * 1)) ⊗ₜ[R, gf] m : (ModuleCat.extendScalars gf).obj M) = _
  rw [mul_one]
  rfl

/-- Commuting a scalar past a pure tensor in an extension of scalars.  The balancing relation
is read off from the `R`-linearity of the unit of the extension/restriction adjunction. -/
theorem tmul_mul_comm (f : R →+* S) (M : ModuleCat.{u} R) (s : S) (r : R) (m : M) :
    (s * f r) ⊗ₜ[R, f] m = s ⊗ₜ[R, f] (r • m) := by
  have h' : (1 : S) ⊗ₜ[R, f] (r • m) = (f r * 1) ⊗ₜ[R, f] m :=
    ((ModuleCat.extendRestrictScalarsAdj f).unit.app M).hom.map_smul r m
  rw [mul_one] at h'
  rw [← ModuleCat.ExtendScalars.smul_tmul f s (f r) m]
  erw [← h']
  erw [ModuleCat.ExtendScalars.smul_tmul f s 1 (r • m)]
  rw [mul_one]

/-- The associativity computation underlying the coherence of the composition comparison. -/
theorem extendScalarsComp'_assoc_apply (f : R →+* S) (g : S →+* T) (h : T →+* U)
    (gf : R →+* T) (hg : S →+* U) (hgf : R →+* U)
    (h₁ : gf = g.comp f) (h₂ : hg = h.comp g) (h₃ : hgf = h.comp gf) (h₄ : hgf = hg.comp f)
    (M : ModuleCat.{u} R) (u : U) (t : T) (s : S) (m : M) :
    (extendScalarsComp' gf h hgf h₃).hom.app M
        (u ⊗ₜ[T, h] (extendScalarsComp' f g gf h₁).hom.app M (t ⊗ₜ[S, g] (s ⊗ₜ[R, f] m))) =
      (extendScalarsComp' f hg hgf h₄).hom.app M
        ((extendScalarsComp' g h hg h₂).hom.app ((ModuleCat.extendScalars f).obj M)
          (u ⊗ₜ[T, h] (t ⊗ₜ[S, g] (s ⊗ₜ[R, f] m)))) := by
  rw [extendScalarsComp'_hom_app_tmul f g gf h₁ M t s m]
  erw [extendScalarsComp'_hom_app_tmul gf h hgf h₃ M u (t * g s) m]
  rw [extendScalarsComp'_hom_app_tmul g h hg h₂ ((ModuleCat.extendScalars f).obj M) u t
      (s ⊗ₜ[R, f] m)]
  erw [extendScalarsComp'_hom_app_tmul f hg hgf h₄ M (u * h t) s m]
  rw [h₂]
  simp only [RingHom.coe_comp, Function.comp_apply, map_mul, mul_assoc]
  rfl

/-- Termwise base change along the identity ring homomorphism is the identity functor. -/
noncomputable def baseChangeIdIso (R : Type u) [CommRing R] :
    baseChangeFunctor (RingHom.id R) ≅ 𝟭 (CochainComplex (ModuleCat.{u} R) ℤ) :=
  NatIso.mapHomologicalComplex (extendScalarsIdIso R) _ ≪≫
    Functor.mapHomologicalComplexIdIso _ _

/-- Termwise base change along a composite ring homomorphism is the composite of the termwise
base changes. -/
noncomputable def baseChangeComp' (f : R →+* S) (g : S →+* T) (gf : R →+* T)
    (hgf : gf = g.comp f) :
    baseChangeFunctor f ⋙ baseChangeFunctor g ≅ baseChangeFunctor gf :=
  Functor.mapHomologicalComplexCompIso (extendScalarsComp' f g gf hgf) _

/-- The identity comparison for termwise base change, computed in each degree. -/
@[simp] theorem baseChangeIdIso_hom_app_f_tmul (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (r : R) (m : K.X n) :
    ((baseChangeIdIso R).hom.app K).f n (r ⊗ₜ[R, RingHom.id R] m) = r • m :=
  extendScalarsIdIso_hom_app_tmul (K.X n) r m

/-- The composition comparison for termwise base change, computed in each degree. -/
@[simp] theorem baseChangeComp'_hom_app_f_tmul (f : R →+* S) (g : S →+* T) (gf : R →+* T)
    (hgf : gf = g.comp f) (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (t : T) (s : S) (m : K.X n) :
    ((baseChangeComp' f g gf hgf).hom.app K).f n (t ⊗ₜ[S, g] (s ⊗ₜ[R, f] m)) =
      (t * g s) ⊗ₜ[R, gf] m :=
  extendScalarsComp'_hom_app_tmul f g gf hgf (K.X n) t s m

set_option backward.isDefEq.respectTransparency false in
/-- Left unit coherence for base change: composing with the identity base change on the left
is the identity comparison. -/
theorem baseChangeComp'_id_left (f : R →+* S) :
    baseChangeComp' (RingHom.id R) f f (RingHom.comp_id f).symm =
      Functor.isoWhiskerRight (baseChangeIdIso R) (baseChangeFunctor f) ≪≫
        (baseChangeFunctor f).leftUnitor := by
  ext K n x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul s y =>
      induction y using TensorProduct.induction_on with
      | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero]
      | tmul r m =>
          exact (baseChangeComp'_hom_app_f_tmul (RingHom.id R) f f _ K n s r m).trans
            (tmul_mul_comm f (K.X n) s r m)
      | add y₁ y₂ k₁ k₂ =>
          rw [TensorProduct.tmul_add, map_add, map_add, k₁, k₂]
  | add x₁ x₂ k₁ k₂ => rw [map_add, map_add, k₁, k₂]

set_option backward.isDefEq.respectTransparency false in
/-- Right unit coherence for base change: composing with the identity base change on the right
is the identity comparison. -/
theorem baseChangeComp'_id_right (f : R →+* S) :
    baseChangeComp' f (RingHom.id S) f (RingHom.id_comp f).symm =
      Functor.isoWhiskerLeft (baseChangeFunctor f) (baseChangeIdIso S) ≪≫
        (baseChangeFunctor f).rightUnitor := by
  ext K n x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul t y =>
      induction y using TensorProduct.induction_on with
      | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero]
      | tmul s m =>
          exact baseChangeComp'_hom_app_f_tmul f (RingHom.id S) f _ K n t s m
      | add y₁ y₂ k₁ k₂ =>
          rw [TensorProduct.tmul_add, map_add, map_add, k₁, k₂]
  | add x₁ x₂ k₁ k₂ => rw [map_add, map_add, k₁, k₂]

set_option maxHeartbeats 800000 in
-- The elaborator must unfold the mate construction underlying the composition comparison.
set_option backward.isDefEq.respectTransparency false in
/-- Associativity coherence for base change: the two ways of comparing a triple composite of
ring homomorphisms agree. -/
theorem baseChangeComp'_assoc (f : R →+* S) (g : S →+* T) (h : T →+* U)
    (gf : R →+* T) (hg : S →+* U) (hgf : R →+* U)
    (h₁ : gf = g.comp f) (h₂ : hg = h.comp g) (h₃ : hgf = h.comp gf) :
    Functor.isoWhiskerRight (baseChangeComp' f g gf h₁) (baseChangeFunctor h) ≪≫
        baseChangeComp' gf h hgf h₃ =
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (baseChangeFunctor f) (baseChangeComp' g h hg h₂) ≪≫
        baseChangeComp' f hg hgf (by rw [h₃, h₁, h₂, RingHom.comp_assoc]) := by
  ext K n x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul u y =>
      induction y using TensorProduct.induction_on with
      | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero]
      | tmul t z =>
          induction z using TensorProduct.induction_on with
          | zero => rw [TensorProduct.tmul_zero, TensorProduct.tmul_zero, map_zero, map_zero]
          | tmul s m =>
              simp only [Iso.trans_hom, NatTrans.comp_app, HomologicalComplex.comp_f,
                ModuleCat.hom_comp, LinearMap.comp_apply, Functor.isoWhiskerRight_hom,
                Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
                Functor.associator_hom_app, Functor.mapHomologicalComplex_map_f,
                HomologicalComplex.id_f]
              exact extendScalarsComp'_assoc_apply f g h gf hg hgf h₁ h₂ h₃
                (by rw [h₃, h₁, h₂, RingHom.comp_assoc]) (K.X n) u t s m
          | add z₁ z₂ k₁ k₂ =>
              rw [TensorProduct.tmul_add, TensorProduct.tmul_add, map_add, map_add, k₁, k₂]
      | add y₁ y₂ k₁ k₂ =>
          rw [TensorProduct.tmul_add, map_add, map_add, k₁, k₂]
  | add x₁ x₂ k₁ k₂ => rw [map_add, map_add, k₁, k₂]

end Pseudofunctor

/-! ## Comparison of the big étale and big fppf ringed sites -/

section SiteComparison

/-- The identity functor is continuous from a coarser to a finer topology on the same site. -/
theorem isContinuous_id_of_le {C : Type u} [Category.{v} C]
    {J K : GrothendieckTopology C} (hJK : J ≤ K) :
    (𝟭 C).IsContinuous J K where
  op_comp_isSheaf_of_types G :=
    (isSheaf_iff_isSheaf_of_type _ _).1 (G.2.of_le hJK)

/-- The big fppf site of schemes, ringed by the representable sheaf of regular functions. -/
def bigFppfSchemeRingedSite : Sites.RingedSite.{u + 1} Sites.Scheme.{u} where
  topology := _root_.AlgebraicGeometry.Scheme.fppfTopology
  structureSheaf :=
    { obj := Sites.regularFunctionsCommRingPresheaf
      property := Sites.regularFunctionsCommRing_isFppfSheaf }

/-- The big étale site of schemes, ringed by the same sheaf of regular functions. -/
def bigEtaleSchemeRingedSite : Sites.RingedSite.{u + 1} Sites.Scheme.{u} where
  topology := _root_.AlgebraicGeometry.Scheme.etaleTopology
  structureSheaf :=
    { obj := Sites.regularFunctionsCommRingPresheaf
      property := Sites.regularFunctionsCommRing_isEtaleSheaf }

/-- The comparison morphism of ringed sites from the big étale site to the big fppf site of
schemes.  The site functor is the identity, its continuity is the inclusion of the étale topology
in the fppf topology, and the structure-sheaf comparison is the identity because both sites carry
the same representable sheaf of regular functions. -/
noncomputable def etaleToFppfRingedSiteMorphism :
    Sites.RingedSiteMorphism.{u + 1, u, u + 1}
      bigEtaleSchemeRingedSite.{u} bigFppfSchemeRingedSite.{u} where
  siteFunctor := 𝟭 _
  continuous := isContinuous_id_of_le Sites.etaleTopology_le_fppfTopology
  structureIso := Iso.refl _

/-- Restriction of module sheaves along the constructed étale/fppf comparison of ringed sites. -/
noncomputable def etaleToFppfModules :
    bigFppfSchemeRingedSite.{u}.Modules ⥤ bigEtaleSchemeRingedSite.{u}.Modules :=
  etaleToFppfRingedSiteMorphism.moduleInverseImage

/-- Restriction of module sheaves along the identity ringed-site morphism of the big étale site
is canonically the identity functor. -/
noncomputable def etaleModuleInverseImageId :
    (Sites.RingedSiteMorphism.id.{u + 1, u, u + 1}
        bigEtaleSchemeRingedSite.{u}).moduleInverseImage ≅
      𝟭 bigEtaleSchemeRingedSite.{u}.Modules :=
  Sites.RingedSiteMorphism.moduleInverseImageId.{u + 1, u, u + 1} _

/-- Restricting module sheaves first along the identity of the big fppf site and then along the
étale/fppf comparison agrees with restricting along the composite ringed-site morphism. -/
noncomputable def etaleToFppfModulesComp :
    (Sites.RingedSiteMorphism.id.{u + 1, u, u + 1}
          bigFppfSchemeRingedSite.{u}).moduleInverseImage ⋙ etaleToFppfModules.{u} ≅
      (etaleToFppfRingedSiteMorphism.{u}.comp
        (Sites.RingedSiteMorphism.id.{u + 1, u, u + 1}
          bigFppfSchemeRingedSite.{u})).moduleInverseImage :=
  Sites.RingedSiteMorphism.moduleInverseImageComp.{u + 1, u, u + 1} _ _

end SiteComparison


end Derived

end GromovWitten.AlgebraicGeometry.Modules
