/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.VirtualFundamentalClass.GlobalCone
import GromovWitten.AlgebraicGeometry.IntersectionTheory.BundlePullbackGlobal

/-!
# The affine obstruction datum as a global cone datum

`VirtualFundamentalClass/GlobalCone.lean` defines a `GlobalConeData` on an arbitrary scheme and
the associated global virtual class, and the affine model of rounds 14–16 defines
`OverField.virtualClass φ` for a closed subscheme `X = Spec (R ⧸ I) ⊆ Spec R` and a chain map
`φ : E ⟶ conormalComplex k R I`.  This file is the acceptance test relating the two: the affine
datum `φ` is turned into a global datum on `X = Spec (R ⧸ I)` with the single chart `⊤`, and the
resulting global virtual class is proved to be the affine one.

The quasi-coherent algebras are obtained by base change of a fixed `(R ⧸ I)`-algebra `S`: the
ring over an affine open `U` is `Γ(X, U) ⊗_{R ⧸ I} S` (`constData`).  This requires an algebra
structure on the section rings of `Spec B` over its opens, which Mathlib does not provide; it is
supplied here by `specSectionsAlgebra` (the identification `Γ(Spec B, ⊤) ≃ B` followed by
restriction).  The base-change squares of `constData` are `Algebra.TensorProduct.cancelBaseChange`.

## Main definitions and results

* `constData`, `constHom`, `constAug` — the constant quasi-coherent algebra `Γ(U) ⊗_B S` on
  `Spec B`, the morphism induced by a `B`-algebra map, and the morphism to the structure sheaf
  induced by an augmentation `S → B`.
* `bundleData φ : BundleData (Spec (CommRingCat.of (R ⧸ I))) _` — the vector bundle
  `E₁ = Spec Sym(E⁻¹)` as a global bundle datum, with the single chart `⊤` and the polynomial
  trivialisation `trivChart` coming from `VirtualClass.trivialization φ`.
* `globalConeData φ : GlobalCone.GlobalConeData (bundleData φ) (fun _ ↦ φ)` — the resolved cone
  `C(E) ⊆ E₁` as a global cone datum.
* `isIso_bundleChartι` — the single chart exhausts the total space, so the affine model
  `ResolvedCone.bundleSpace φ` *is* the total space; `chartRestrict` and `chartExtend` are the
  resulting mutually inverse maps on rational Chow groups.
* `chartRestrict_coneClassAt` — the global cone class is the affine resolved-cone class.
* `chowPullback` — the flat pullback along the bundle projection, obtained by transporting
  `VirtualClass.bundlePullback φ` along the chart isomorphism; it is injective
  (`chowPullback_injective`) and hits the global cone class (`coneClassAt_mem_range`), so it
  discharges the three hypotheses `pull`, `hinj`, `hmem` of `GlobalCone.virtualClassOf` in this
  case.
* `virtualClassOf_eq_virtualClass` — **the acceptance test**: the global virtual class of
  `globalConeData φ` for this pullback is `OverField.virtualClass φ`.

## What is not proved here

The construction uses only the chart identification `chartBundle` of `GlobalConeData`, never the
polynomial trivialisation `BundleData.triv`; consequently the comparison of the global cycle
pullback `IntersectionTheory.BundlePullbackGlobal.pullbackBundle (bundleData φ)` with the affine
`AlgebraicCycle.pullbackBundle (VirtualClass.trivialization φ)` is not carried out (it needs the
missing compatibility between `chartBundle` and `triv`, open item 1 of the report on
`GlobalCone.lean`).  The dimension comparison `hdim` between the certified dimension function of
the total space and that of the affine bundle space is an explicit hypothesis, exactly as in
`cyclesOfDimension.flatPullbackOpen`.
-/

universe u

set_option maxSynthPendingDepth 5

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace GromovWitten.AlgebraicGeometry

open IntersectionTheory hiding Scheme AlgebraicCycle
open VectorBundleTotalSpace RelativeSpec
open VirtualFundamentalClass
open GlobalBlowup (res isAffineOpen res_refl res_comp)

namespace VirtualClass.GlobalConeAffine

noncomputable section

/-! ## Sections of the structure sheaf of an affine scheme as an algebra -/

section Sections

variable (B : Type u) [CommRing B]

/-- The sections of `𝒪_{Spec B}` over an open subset form a `B`-algebra, via the identification
`Γ(Spec B, ⊤) ≃ B` followed by restriction. -/
instance specSectionsAlgebra (U : (Spec (CommRingCat.of B)).Opens) :
    Algebra B Γ(Spec (CommRingCat.of B), U) :=
  (((Spec (CommRingCat.of B)).presheaf.map (homOfLE (le_top (a := U))).op).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom).toAlgebra

/-- The restriction maps of `Spec B` are `B`-algebra maps. -/
theorem res_algebraMap {U V : (Spec (CommRingCat.of B)).affineOpens} (h : U ≤ V) (b : B) :
    res (Spec (CommRingCat.of B)) h (algebraMap B Γ(Spec (CommRingCat.of B), V.1) b) =
      algebraMap B Γ(Spec (CommRingCat.of B), U.1) b := by
  change ((Spec (CommRingCat.of B)).presheaf.map _).hom
      (((Spec (CommRingCat.of B)).presheaf.map _).hom _) = _
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- The restriction map between the sections over two affine opens of `Spec B`, as a
`B`-algebra map. -/
def resₐ {U V : (Spec (CommRingCat.of B)).affineOpens} (h : U ≤ V) :
    Γ(Spec (CommRingCat.of B), V.1) →ₐ[B] Γ(Spec (CommRingCat.of B), U.1) :=
  { res (Spec (CommRingCat.of B)) h with commutes' := res_algebraMap B h }

/-- `resₐ` is the restriction map. -/
@[simp]
theorem resₐ_apply {U V : (Spec (CommRingCat.of B)).affineOpens} (h : U ≤ V)
    (a : Γ(Spec (CommRingCat.of B), V.1)) :
    resₐ B h a = res (Spec (CommRingCat.of B)) h a := rfl

end Sections

/-! ## The constant quasi-coherent algebra attached to an algebra -/

section ConstData

variable (B : Type u) [CommRing B] (S : Type u) [CommRing S] [Algebra B S]

/-- Two ring maps out of a tensor product agree as soon as they agree on pure tensors. -/
theorem ringHom_ext_tensor {A T : Type u} [CommRing A] [Algebra B A] [CommRing T]
    {f g : A ⊗[B] S →+* T} (h : ∀ (a : A) (s : S), f (a ⊗ₜ[B] s) = g (a ⊗ₜ[B] s)) : f = g := by
  refine RingHom.ext fun x ↦ ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a s => exact h a s
  | add x y hx hy => simp [hx, hy]

/-- The quasi-coherent algebra on `Spec B` obtained by base change of a fixed `B`-algebra `S`:
the ring over an affine open `U` is `Γ(U) ⊗[B] S`, and the transition maps are the restriction
maps of `𝒪_{Spec B}` tensored with the identity. -/
def constData : AlgebraData (Spec (CommRingCat.of B)) where
  ring U := Γ(Spec (CommRingCat.of B), U.1) ⊗[B] S
  map h := (Algebra.TensorProduct.map (resₐ B h) (AlgHom.id B S)).toRingHom
  map_id U := by
    refine ringHom_ext_tensor B S fun a s ↦ ?_
    simp [res_refl]
  map_comp hUV hVW := by
    refine ringHom_ext_tensor B S fun a s ↦ ?_
    simp [res_comp _ hUV hVW]
  isPushout {U V} h := by
    let _ := (res (Spec (CommRingCat.of B)) h).toAlgebra
    have hst : IsScalarTower B Γ(Spec (CommRingCat.of B), V.1)
        Γ(Spec (CommRingCat.of B), U.1) :=
      IsScalarTower.of_algebraMap_eq fun b ↦ (res_algebraMap B h b).symm
    refine isPushout_of_algEquiv _ (Algebra.TensorProduct.cancelBaseChange B
      Γ(Spec (CommRingCat.of B), V.1) Γ(Spec (CommRingCat.of B), U.1)
      Γ(Spec (CommRingCat.of B), U.1) S) fun z ↦ ?_
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a s =>
        simp only [Algebra.TensorProduct.cancelBaseChange_tmul]
        congr 1
        change algebraMap Γ(Spec (CommRingCat.of B), V.1) Γ(Spec (CommRingCat.of B), U.1) a * 1 = _
        rw [mul_one]
        rfl
    | add x y hx hy => simp [TensorProduct.tmul_add, hx, hy]

/-- The transition maps of `constData` on pure tensors. -/
@[simp]
theorem constData_map_tmul {U V : (Spec (CommRingCat.of B)).affineOpens} (h : U ≤ V)
    (a : Γ(Spec (CommRingCat.of B), V.1)) (s : S) :
    (constData B S).map h (a ⊗ₜ[B] s) = res (Spec (CommRingCat.of B)) h a ⊗ₜ[B] s := rfl

/-- The ring of `constData` over an affine open. -/
@[simp]
theorem constData_ring (U : (Spec (CommRingCat.of B)).affineOpens) :
    (constData B S).ring U = (Γ(Spec (CommRingCat.of B), U.1) ⊗[B] S) := rfl

/-- The identification `Γ(Spec B, ⊤) ≃ B` as an isomorphism of `B`-algebras. -/
def topAlgEquiv : Γ(Spec (CommRingCat.of B), (⊤ : (Spec (CommRingCat.of B)).Opens)) ≃ₐ[B] B :=
  { (Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv with
    commutes' := fun b ↦ by
      change (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom
        (((Spec (CommRingCat.of B)).presheaf.map _).hom _) = _
      rw [show (homOfLE (le_top (a := (⊤ : (Spec (CommRingCat.of B)).Opens)))).op = 𝟙 _ from
        Subsingleton.elim _ _, CategoryTheory.Functor.map_id]
      change (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b) = b
      rw [← CommRingCat.comp_apply, Iso.inv_hom_id]
      rfl }

/-- `topAlgEquiv` is the global-sections identification. -/
@[simp]
theorem topAlgEquiv_apply
    (a : Γ(Spec (CommRingCat.of B), (⊤ : (Spec (CommRingCat.of B)).Opens))) :
    topAlgEquiv B a = (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom a := rfl

/-- Over the chart `⊤` the constant quasi-coherent algebra is `S` itself. -/
def constTopEquiv :
    (Γ(Spec (CommRingCat.of B), (⊤ : (Spec (CommRingCat.of B)).Opens)) ⊗[B] S) ≃ₐ[B] S :=
  (Algebra.TensorProduct.congr (topAlgEquiv B) AlgEquiv.refl).trans
    (Algebra.TensorProduct.lid B S)

/-- `constTopEquiv` on pure tensors. -/
@[simp]
theorem constTopEquiv_tmul
    (a : Γ(Spec (CommRingCat.of B), (⊤ : (Spec (CommRingCat.of B)).Opens))) (s : S) :
    constTopEquiv B S (a ⊗ₜ[B] s) = topAlgEquiv B a • s := rfl

end ConstData

section ConstHom

variable (B : Type u) [CommRing B] (S T : Type u) [CommRing S] [Algebra B S] [CommRing T]
  [Algebra B T]

/-- A `B`-algebra map `S → T` induces a morphism of the associated quasi-coherent algebras. -/
def constHom (f : S →ₐ[B] T) :
    RelativeSpec.Hom (Spec (CommRingCat.of B)) (constData B T) (constData B S) where
  app U := Algebra.TensorProduct.map
    (AlgHom.id Γ(Spec (CommRingCat.of B), U.1) Γ(Spec (CommRingCat.of B), U.1)) f
  naturality h := by
    refine ringHom_ext_tensor B S fun a s ↦ ?_
    rfl

/-- The components of `constHom` on pure tensors. -/
@[simp]
theorem constHom_app_tmul (f : S →ₐ[B] T) (U : (Spec (CommRingCat.of B)).affineOpens)
    (a : Γ(Spec (CommRingCat.of B), U.1)) (s : S) :
    (constHom B S T f).app U (a ⊗ₜ[B] s) = a ⊗ₜ[B] f s := rfl

/-- A surjective algebra map induces surjective components. -/
theorem surjective_constHom_app (f : S →ₐ[B] T) (hf : Function.Surjective f)
    (U : (Spec (CommRingCat.of B)).affineOpens) :
    Function.Surjective ((constHom B S T f).app U) := by
  intro y
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a t =>
      obtain ⟨s, rfl⟩ := hf t
      exact ⟨a ⊗ₜ[B] s, rfl⟩
  | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', map_add _ _ _⟩

/-- The component over an affine open of the morphism induced by an augmentation `S → B`. -/
def constAugApp (ε : S →ₐ[B] B) (U : (Spec (CommRingCat.of B)).affineOpens) :
    (Γ(Spec (CommRingCat.of B), U.1) ⊗[B] S) →ₐ[Γ(Spec (CommRingCat.of B), U.1)]
      Γ(Spec (CommRingCat.of B), U.1) :=
  Algebra.TensorProduct.lift
    (AlgHom.id Γ(Spec (CommRingCat.of B), U.1) Γ(Spec (CommRingCat.of B), U.1))
    ((Algebra.ofId B Γ(Spec (CommRingCat.of B), U.1)).comp ε) fun _ _ ↦ Commute.all _ _

/-- An augmentation `S → B` induces a morphism from the structure sheaf to the associated
quasi-coherent algebra, i.e. a section of the associated relative `Spec`. -/
def constAug (ε : S →ₐ[B] B) :
    RelativeSpec.Hom (Spec (CommRingCat.of B)) (structureData (Spec (CommRingCat.of B)))
      (constData B S) where
  app U := constAugApp B S ε U
  naturality h := by
    refine ringHom_ext_tensor B S fun a s ↦ ?_
    change res _ h a * algebraMap B _ (ε s) = res _ h (a * algebraMap B _ (ε s))
    rw [map_mul, res_algebraMap]

/-- The components of `constAug` on pure tensors. -/
@[simp]
theorem constAug_app_tmul (ε : S →ₐ[B] B) (U : (Spec (CommRingCat.of B)).affineOpens)
    (a : Γ(Spec (CommRingCat.of B), U.1)) (s : S) :
    (constAug B S ε).app U (a ⊗ₜ[B] s) = a * algebraMap B Γ(Spec (CommRingCat.of B), U.1) (ε s) :=
  rfl

end ConstHom

/-! ## The global bundle datum of an affine obstruction datum -/

section Affine

open NormalSheafPicard.AffineIntrinsicNormalSheaf

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] [IsNoetherianRing R]
  {I : Ideal R} {E : LinearTwoTermComplex (R ⧸ I)}
  [Module.Free (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) E.degreeZero]
  (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))

/-- Evaluating a polynomial with coefficients extended along `A → C` at the origin is the image
of the evaluation at the origin. -/
theorem aeval_zero_map {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] {σ : Type u}
    (p : MvPolynomial σ A) :
    MvPolynomial.aeval (fun _ ↦ (0 : C)) (MvPolynomial.map (algebraMap A C) p) =
      algebraMap A C (MvPolynomial.aeval (fun _ ↦ (0 : A)) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp
  | mul_X p n hp => simp

/-- The augmentation of `Sym(E⁻¹)`, i.e. evaluation at the origin of `E₁`, read off from the
polynomial trivialisation. -/
def augmentationAlg : ResolvedCone.bundleRing φ →ₐ[R ⧸ I] (R ⧸ I) :=
  (MvPolynomial.aeval fun _ ↦ (0 : R ⧸ I)).comp
    (VirtualClass.trivialization φ).toAlgHom

/-- The trivialisation of the global bundle over an affine open. -/
def trivChart (U : (Spec (CommRingCat.of (R ⧸ I))).affineOpens) :
    (Γ(Spec (CommRingCat.of (R ⧸ I)), U.1) ⊗[R ⧸ I] ResolvedCone.bundleRing φ)
      ≃ₐ[Γ(Spec (CommRingCat.of (R ⧸ I)), U.1)]
      MvPolynomial (Module.Free.ChooseBasisIndex (R ⧸ I) E.degreeZero)
        Γ(Spec (CommRingCat.of (R ⧸ I)), U.1) :=
  (Algebra.TensorProduct.congr AlgEquiv.refl (VirtualClass.trivialization φ)).trans
    (MvPolynomial.algebraTensorAlgEquiv (R ⧸ I) Γ(Spec (CommRingCat.of (R ⧸ I)), U.1))

omit [IsNoetherianRing R] [Module.Finite (R ⧸ I) E.degreeZero] in
/-- Over a chart the augmentation of the global bundle datum is evaluation at the origin
in the polynomial coordinates supplied by `trivChart`. -/
theorem constAug_eq_aeval_trivChart (U : (Spec (CommRingCat.of (R ⧸ I))).affineOpens)
    (a : Γ(Spec (CommRingCat.of (R ⧸ I)), U.1) ⊗[R ⧸ I] ResolvedCone.bundleRing φ) :
    constAugApp (R ⧸ I) (ResolvedCone.bundleRing φ) (augmentationAlg φ) U a =
      MvPolynomial.aeval (fun _ ↦ 0) (trivChart φ U a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x s =>
      change x * algebraMap (R ⧸ I) _ (MvPolynomial.aeval _ (VirtualClass.trivialization φ s)) = _
      change _ = MvPolynomial.aeval (fun _ ↦ 0)
        (MvPolynomial.algebraTensorAlgEquiv (R ⧸ I) _ (x ⊗ₜ VirtualClass.trivialization φ s))
      rw [MvPolynomial.algebraTensorAlgEquiv_tmul, map_smul, aeval_zero_map, smul_eq_mul]
  | add x y hx hy => simp [hx, hy]

/-- **The global vector bundle `E₁` of an affine obstruction datum**, with the single chart
`⊤ ⊆ Spec (R ⧸ I)`. -/
def bundleData : BundleData (Spec (CommRingCat.of (R ⧸ I)))
    (Module.Free.ChooseBasisIndex (R ⧸ I) E.degreeZero) where
  algebra := constData (R ⧸ I) (ResolvedCone.bundleRing φ)
  augmentation := constAug (R ⧸ I) (ResolvedCone.bundleRing φ) (augmentationAlg φ)
  J := PUnit.{u + 1}
  chart _ := ⟨⊤, isAffineOpen_top _⟩
  iSup_chart := by simp
  triv _ := trivChart φ ⟨⊤, isAffineOpen_top _⟩
  augmentation_triv _ a := constAug_eq_aeval_trivChart φ ⟨⊤, isAffineOpen_top _⟩ a

/-- **The global cone datum of an affine obstruction datum.**  The quasi-coherent algebra of the
cone is the base change of the affine resolved-cone ring, and over the single chart `⊤` all the
identifications are the canonical ones. -/
def globalConeData : GlobalCone.GlobalConeData (k := k) (bundleData φ)
    (R := fun _ ↦ R) (I := fun _ ↦ I) (E := fun _ ↦ E) (fun _ ↦ φ) where
  cone := constData (R ⧸ I) (ResolvedCone.ring φ)
  inclusion := constHom (R ⧸ I) (ResolvedCone.bundleRing φ) (ResolvedCone.ring φ)
    (Ideal.Quotient.mkₐ (R ⧸ I) (ResolvedCone.ideal φ))
  surjective_inclusion U :=
    surjective_constHom_app (R ⧸ I) (ResolvedCone.bundleRing φ) (ResolvedCone.ring φ) _
      Ideal.Quotient.mk_surjective U
  chartBase _ := (topAlgEquiv (R ⧸ I)).toRingEquiv
  chartBundle _ := (constTopEquiv (R ⧸ I) (ResolvedCone.bundleRing φ)).toRingEquiv
  chartBundle_algebraMap _ r := by
    change constTopEquiv (R ⧸ I) (ResolvedCone.bundleRing φ) (r ⊗ₜ[R ⧸ I] 1) = _
    rw [constTopEquiv_tmul, Algebra.smul_def, mul_one]
    rfl
  chartCone _ := (constTopEquiv (R ⧸ I) (ResolvedCone.ring φ)).toRingEquiv
  chartCone_inclusion _ a := by
    induction a using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x s =>
        change constTopEquiv (R ⧸ I) (ResolvedCone.ring φ)
          (x ⊗ₜ[R ⧸ I] Ideal.Quotient.mk (ResolvedCone.ideal φ) s) = _
        rw [constTopEquiv_tmul]
        change _ = Ideal.Quotient.mk (ResolvedCone.ideal φ)
          (constTopEquiv (R ⧸ I) (ResolvedCone.bundleRing φ) (x ⊗ₜ[R ⧸ I] s))
        rw [constTopEquiv_tmul, Algebra.smul_def, Algebra.smul_def, map_mul]
        rfl
    | add x y hx hy => simp only [map_add, hx, hy]

/-- The coordinate rings of the cone algebra are Noetherian. -/
theorem isNoetherianRing_cone_ring (U : (Spec (CommRingCat.of (R ⧸ I))).affineOpens) :
    IsNoetherianRing ((globalConeData φ).cone.ring U) := by
  have h1 : IsNoetherianRing Γ(Spec (CommRingCat.of (R ⧸ I)), U.1) :=
    IsLocallyNoetherian.component_noetherian U
  have h2 : IsNoetherianRing (MvPolynomial (Module.Free.ChooseBasisIndex (R ⧸ I) E.degreeZero)
      Γ(Spec (CommRingCat.of (R ⧸ I)), U.1)) := inferInstance
  have h3 : IsNoetherianRing (Γ(Spec (CommRingCat.of (R ⧸ I)), U.1) ⊗[R ⧸ I]
      ResolvedCone.bundleRing φ) :=
    isNoetherianRing_of_ringEquiv _ (trivChart φ U).symm.toRingEquiv
  have h4 : IsNoetherianRing ((constData (R ⧸ I) (ResolvedCone.bundleRing φ)).ring U) := h3
  exact isNoetherianRing_of_surjective _ _
    ((constHom (R ⧸ I) (ResolvedCone.bundleRing φ) (ResolvedCone.ring φ)
      (Ideal.Quotient.mkₐ (R ⧸ I) (ResolvedCone.ideal φ))).app U).toRingHom
    (surjective_constHom_app (R ⧸ I) (ResolvedCone.bundleRing φ) (ResolvedCone.ring φ) _
      Ideal.Quotient.mk_surjective U)

/-- The global cone of an affine obstruction datum is a locally Noetherian scheme. -/
instance isLocallyNoetherian_coneScheme :
    IsLocallyNoetherian ((globalConeData φ).coneScheme) :=
  (globalConeData φ).isLocallyNoetherian_coneScheme (isNoetherianRing_cone_ring φ)

end Affine

/-! ## Chart isomorphisms and Chow groups -/

section ChartIso

/-- The affine piece of a relative `Spec` over the whole of an affine base is an isomorphism. -/
theorem isIso_affineι_top {X : Scheme.{u}} (𝒜 : AlgebraData X)
    (hU : IsAffineOpen (⊤ : X.Opens)) : IsIso (affineι X 𝒜 ⟨⊤, hU⟩) := by
  refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
  rw [opensRange_affineι]
  simp

variable {X U : Scheme.{u}} {dX : DimensionFunction X} {dU : DimensionFunction U} {i : ℤ}

/-- Two mutually inverse open immersions induce mutually inverse flat pullbacks of graded
cycles. -/
theorem flatPullbackOpen_comp_eq_self (j : U ⟶ X) (g : X ⟶ U)
    [IsOpenImmersion j] [IsOpenImmersion g] (hgj : g ≫ j = 𝟙 X)
    (h₁ : ∀ u, dU u = dX (j.base u)) (h₂ : ∀ x, dX x = dU (g.base x))
    (z : cyclesOfDimension X dX i) :
    cyclesOfDimension.flatPullbackOpen g h₂ (cyclesOfDimension.flatPullbackOpen j h₁ z) = z := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.coe_injective
  funext x
  change (z : AlgebraicCycle X ℚ) (j.base (g.base x)) = (z : AlgebraicCycle X ℚ) x
  rw [show j.base (g.base x) = (g ≫ j).base x from rfl, hgj]
  rfl

/-- Two mutually inverse open immersions induce mutually inverse pullbacks of rational Chow
classes. -/
theorem openImmersionPullback_comp_eq_self
    (Rx : RationalEquivalenceSystem X dX i) (S : RationalEquivalenceSystem U dU i)
    (j : U ⟶ X) (g : X ⟶ U) [IsOpenImmersion j] [IsOpenImmersion g] (hgj : g ≫ j = 𝟙 X)
    (h₁ : ∀ u, dU u = dX (j.base u)) (h₂ : ∀ x, dX x = dU (g.base x)) :
    (RationalEquivalenceSystem.DescendingMap.openImmersionPullback S g h₂ Rx).comp
        (RationalEquivalenceSystem.DescendingMap.openImmersionPullback Rx j h₁ S) =
      LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨z⟩
  change Rx.quotientMap (cyclesOfDimension.flatPullbackOpen g h₂
    (cyclesOfDimension.flatPullbackOpen j h₁ z)) = Rx.quotientMap z
  rw [flatPullbackOpen_comp_eq_self j g hgj h₁ h₂ z]

end ChartIso

/-! ## The global virtual class of an affine obstruction datum -/

section Comparison

open NormalSheafPicard.AffineIntrinsicNormalSheaf
open RationalEquivalenceSystem.DescendingMap

variable {k R : Type u} [Field k] [Infinite k] [CommRing R] [Algebra k R]
  [Algebra.FiniteType k R] [IsNoetherianRing R] {I : Ideal R} [Nontrivial (R ⧸ I)]
  {E : LinearTwoTermComplex (R ⧸ I)}
  [Module.Free (R ⧸ I) E.degreeZero] [Module.Finite (R ⧸ I) E.degreeZero]
  (φ : LinearTwoTermComplex.Hom E (conormalComplex k R I))

/-- The unique chart index of the global bundle datum of an affine obstruction datum. -/
def chartPoint : (bundleData φ).J := PUnit.unit

/-- For the global cone datum of an affine obstruction datum the single chart exhausts the
total space: the chart morphism is an isomorphism. -/
instance isIso_bundleChartι : IsIso ((globalConeData φ).bundleChartι (chartPoint φ)) := by
  have h : IsIso (affineι (Spec (CommRingCat.of (R ⧸ I))) (bundleData φ).algebra
      ((bundleData φ).chart (chartPoint φ))) := isIso_affineι_top _ _
  exact IsIso.comp_isIso' (GlobalCone.GlobalConeData.isIso_specMap_chartBundle _ _) h

variable (dimX : DimensionFunction (Spec (CommRingCat.of (R ⧸ I))))
  (dimE : DimensionFunction (bundleData φ).totalSpace)
  (dimC : DimensionFunction (ResolvedCone.bundleSpace φ))
  (hdim : ∀ y, dimC y = dimE (((globalConeData φ).bundleChartι (chartPoint φ)).base y))

omit [Infinite k] [Algebra.FiniteType k R] [IsNoetherianRing R] [Nontrivial (R ⧸ I)]
  [Module.Finite (R ⧸ I) E.degreeZero] in
include hdim in
/-- The dimension comparison along the inverse of the chart isomorphism. -/
theorem dim_inv (q : (bundleData φ).totalSpace) :
    dimE q = dimC ((inv ((globalConeData φ).bundleChartι (chartPoint φ))).base q) := by
  have h : (inv ((globalConeData φ).bundleChartι (chartPoint φ)) ≫
      (globalConeData φ).bundleChartι (chartPoint φ)).base q = q := by
    rw [IsIso.inv_hom_id]
    rfl
  rw [hdim, show ((globalConeData φ).bundleChartι (chartPoint φ)).base
    ((inv ((globalConeData φ).bundleChartι (chartPoint φ))).base q) = q from h]

variable (RX : RationalEquivalenceSystem (Spec (CommRingCat.of (R ⧸ I))) dimX
    (VirtualClass.virtualDimension φ))
  (RE : RationalEquivalenceSystem (bundleData φ).totalSpace dimE (VirtualClass.coneDegree φ))
  (RC : RationalEquivalenceSystem (ResolvedCone.bundleSpace φ) dimC (VirtualClass.coneDegree φ))

/-- Restriction of rational Chow classes of the total space to the single affine chart. -/
def chartRestrict : RE.ChowGroup →ₗ[ℚ] RC.ChowGroup :=
  openImmersionPullback RE ((globalConeData φ).bundleChartι (chartPoint φ)) hdim RC

/-- The inverse of `chartRestrict`, i.e. pullback along the inverse chart isomorphism. -/
def chartExtend : RC.ChowGroup →ₗ[ℚ] RE.ChowGroup :=
  openImmersionPullback RC (inv ((globalConeData φ).bundleChartι (chartPoint φ)))
    (dim_inv φ dimE dimC hdim) RE

omit [Infinite k] [Algebra.FiniteType k R] [IsNoetherianRing R] [Nontrivial (R ⧸ I)]
  [Module.Finite (R ⧸ I) E.degreeZero] in
/-- Restricting a Chow class of the total space to the chart and extending back is the
identity. -/
theorem chartExtend_chartRestrict (α : RE.ChowGroup) :
    chartExtend φ dimE dimC hdim RE RC (chartRestrict φ dimE dimC hdim RE RC α) = α :=
  LinearMap.congr_fun (openImmersionPullback_comp_eq_self RE RC
    ((globalConeData φ).bundleChartι (chartPoint φ))
    (inv ((globalConeData φ).bundleChartι (chartPoint φ)))
    (IsIso.inv_hom_id _) hdim (dim_inv φ dimE dimC hdim)) α

omit [Infinite k] [Algebra.FiniteType k R] [IsNoetherianRing R] [Nontrivial (R ⧸ I)]
  [Module.Finite (R ⧸ I) E.degreeZero] in
/-- Extending a Chow class of the chart to the total space and restricting back is the
identity. -/
theorem chartRestrict_chartExtend (β : RC.ChowGroup) :
    chartRestrict φ dimE dimC hdim RE RC (chartExtend φ dimE dimC hdim RE RC β) = β :=
  LinearMap.congr_fun (openImmersionPullback_comp_eq_self RC RE
    (inv ((globalConeData φ).bundleChartι (chartPoint φ)))
    ((globalConeData φ).bundleChartι (chartPoint φ))
    (IsIso.hom_inv_id _) (dim_inv φ dimE dimC hdim) hdim) β

omit [Infinite k] [Algebra.FiniteType k R] [Nontrivial (R ⧸ I)] in
/-- **The global cone class is the affine resolved-cone class.** -/
theorem chartRestrict_coneClassAt :
    chartRestrict φ dimE dimC hdim RE RC
        ((globalConeData φ).coneClassAt dimE (VirtualClass.coneDegree φ) RE) =
      VirtualClass.resolvedConeClass φ dimC RC := by
  change RC.quotientMap (cyclesOfDimension.flatPullbackOpen _ hdim
    (cyclesOfDimension.project ((globalConeData φ).coneCycle dimE))) = _
  rw [cyclesOfDimension.flatPullbackOpen_project,
    (globalConeData φ).coneCycleAt_eq_resolvedConeCycleAt dimE (chartPoint φ)
      (VirtualClass.coneDegree φ) dimC]
  rfl

/-- **The flat pullback along the bundle projection** for the global bundle datum of an affine
obstruction datum: the affine bundle pullback transported along the chart isomorphism. -/
def chowPullback : RX.ChowGroup →ₗ[ℚ] RE.ChowGroup :=
  (chartExtend φ dimE dimC hdim RE RC).comp (VirtualClass.bundlePullback φ dimX dimC RX RC)

omit [Infinite k] [Algebra.FiniteType k R] [Nontrivial (R ⧸ I)] in
/-- The flat pullback restricted to the chart is the affine bundle pullback. -/
theorem chartRestrict_chowPullback (α : RX.ChowGroup) :
    chartRestrict φ dimE dimC hdim RE RC
        (chowPullback φ dimX dimE dimC hdim RX RE RC α) =
      VirtualClass.bundlePullback φ dimX dimC RX RC α :=
  chartRestrict_chartExtend φ dimE dimC hdim RE RC _

/-- The flat pullback along the bundle projection is injective. -/
theorem chowPullback_injective :
    Function.Injective (chowPullback φ dimX dimE dimC hdim RX RE RC) := by
  intro a b hab
  refine OverField.hinjOf φ dimX dimC RX RC ?_
  rw [← chartRestrict_chowPullback φ dimX dimE dimC hdim RX RE RC a,
    ← chartRestrict_chowPullback φ dimX dimE dimC hdim RX RE RC b, hab]

/-- **The affine virtual class pulls back to the global cone class.** -/
theorem chowPullback_virtualClass :
    chowPullback φ dimX dimE dimC hdim RX RE RC (OverField.virtualClass φ dimX dimC RX RC) =
      (globalConeData φ).coneClassAt dimE (VirtualClass.coneDegree φ) RE := by
  change chartExtend φ dimE dimC hdim RE RC (VirtualClass.bundlePullback φ dimX dimC RX RC
    (OverField.virtualClass φ dimX dimC RX RC)) = _
  rw [OverField.pullback_virtualClass, ← chartRestrict_coneClassAt φ dimE dimC hdim RE RC,
    chartExtend_chartRestrict]

/-- The global cone class lies in the image of the flat pullback. -/
theorem coneClassAt_mem_range :
    (globalConeData φ).coneClassAt dimE (VirtualClass.coneDegree φ) RE ∈
      LinearMap.range (chowPullback φ dimX dimE dimC hdim RX RE RC) :=
  ⟨_, chowPullback_virtualClass φ dimX dimE dimC hdim RX RE RC⟩

/-- **The acceptance test: the global virtual class of an affine obstruction datum is the
affine virtual class.** -/
theorem virtualClassOf_eq_virtualClass :
    (globalConeData φ).virtualClassOf dimE dimX (VirtualClass.virtualDimension φ)
        (VirtualClass.coneDegree φ) RX RE (chowPullback φ dimX dimE dimC hdim RX RE RC)
        (coneClassAt_mem_range φ dimX dimE dimC hdim RX RE RC) =
      OverField.virtualClass φ dimX dimC RX RC :=
  ((globalConeData φ).virtualClassOf_unique dimE dimX (VirtualClass.virtualDimension φ)
    (VirtualClass.coneDegree φ) RX RE (chowPullback φ dimX dimE dimC hdim RX RE RC)
    (chowPullback_injective φ dimX dimE dimC hdim RX RE RC)
    (coneClassAt_mem_range φ dimX dimE dimC hdim RX RE RC)
    (OverField.virtualClass φ dimX dimC RX RC)
    (chowPullback_virtualClass φ dimX dimE dimC hdim RX RE RC)).symm

end Comparison

end

end VirtualClass.GlobalConeAffine

end GromovWitten.AlgebraicGeometry
