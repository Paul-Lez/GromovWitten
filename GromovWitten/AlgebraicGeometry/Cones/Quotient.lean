/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Fable 5.1
-/

import GromovWitten.AlgebraicGeometry.Cones.Graded
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.CategoryTheory.Category.Cat

/-!
# Cone quotients by vector-bundle actions

Let `C = Spec S` be an affine cone over `Spec R`, encoded as in
`GromovWitten.AlgebraicGeometry.Cones.Graded` by its `𝔸¹`-contraction coaction
`ψ : S →ₐ[R] S[t]`, and let `E = Spec Sym(F)` be the affine vector bundle attached to an
`R`-module `F`.  An action of `E` on `C` compatible with the cone structures is a coaction

`α : S →ₐ[R] S ⊗[R] Sym(F)`

satisfying the comodule axioms and intertwining the two contraction coactions.  This file
constructs that notion, the induced action on points, the quotient groupoid `[C/E]`, its
vertex, its contraction action, equivariant morphisms, homotopy `2`-cells, and a criterion
for two quotient presentations to have equivalent quotients.

## Main definitions

* `ConeQuotient.symComul`, `ConeQuotient.symMap`: the Hopf comultiplication of `Sym(F)` (the
  coordinate algebra of the addition of `E`) and the coordinate algebra map of a morphism of
  vector bundles.
* `ConeQuotient.translate`: the action of the `B`-points `F →ₗ[R] B` of `E` on the `B`-points
  `S →ₐ[R] B` of `C` induced by a coaction.
* `ConeQuotient.ConeAction`: the bundled datum of a cone together with a compatible action of a
  vector bundle.  Its `Prop` fields are the monoid-action axioms on points and the requirement
  that the action map be a morphism of cones; they are hypotheses about the coaction, and are
  *proved* for every action constructed here.
* `ConeQuotient.QuotientGroupoid`: the quotient groupoid `[C/E](B)`, with objects the
  `B`-points of `C` and arrows the `B`-points of `E` that translate one into the other, together
  with its `Category` and `Groupoid` instances.
* `ConeQuotient.QuotientGroupoid.contractionFunctor`, `ConeQuotient.QuotientGroupoid.vertexPoint`,
  `ConeQuotient.QuotientGroupoid.mapQuotient`, `ConeQuotient.quotientPrestack`: the contraction
  action on the quotient, its vertex, reindexing along a map of test algebras, and the resulting
  functor `CommAlgCat R ⥤ Cat`.
* `ConeQuotient.IsEquivariant`, `ConeQuotient.quotientFunctor`, `ConeQuotient.Homotopy`,
  `ConeQuotient.Homotopy.natIso`: equivariant morphisms of cones with actions, the induced
  functor of quotient groupoids, homotopies between equivariant morphisms, and the `2`-cell
  they induce.
* `ConeQuotient.translationAction`, `ConeQuotient.freeAction`: the translation action of `E` on
  itself and the free action of `E` on a product `C ×_{Spec R} E`.
* `ConeQuotient.IsExactSequence`: exactness of a sequence of cones `E → C → D`.
* `ConeQuotient.actionMap`, `ConeQuotient.zeroSectionMap`: the action and the zero section as
  morphisms of affine schemes.

## Main results

* `ConeQuotient.ConeAction.scale_translate`: contractions commute with the action, so the action
  is `𝔾ₘ`-equivariant; `ConeQuotient.ConeAction.scale_vertex` and
  `ConeQuotient.ConeAction.scale_zero_eq` describe the vertex.
* `ConeQuotient.QuotientGroupoid.contractionOneIso`,
  `ConeQuotient.QuotientGroupoid.contractionMulIso`,
  `ConeQuotient.QuotientGroupoid.contractionZeroIso`: the contraction action laws on the
  quotient groupoid.
* `ConeQuotient.QuotientGroupoid.mapQuotient_id`,
  `ConeQuotient.QuotientGroupoid.mapQuotient_comp`,
  `ConeQuotient.QuotientGroupoid.mapQuotient_comp_contractionFunctor`: the quotient groupoids
  are strictly functorial in the test algebra, and all cone actions commute with reindexing.
* `ConeQuotient.isEquivalence_quotientFunctor`: the criterion for two quotient presentations to
  have equivalent quotient groupoids.
* `ConeQuotient.translationQuotientEquivalence`: the quotient of a vector bundle by its own
  translation action is the base, `[E/E] ≃ Spec R`.
* `ConeQuotient.freeQuotientEquivalence` and
  `ConeQuotient.IsExactSequence.quotientEquivalence`: a free quotient is the honest quotient,
  so `[C ×_{Spec R} E / E] ≃ C`, and more generally the quotient of an exact sequence
  `E → C → D` is `D`.
* `ConeQuotient.zeroSectionMap_comp_actionMap`,
  `ConeQuotient.actionMap_comp_contractionMap`: the unit law and the `𝔾ₘ`-equivariance of the
  action, as morphisms of schemes.

-/

open CategoryTheory

namespace GromovWitten.AlgebraicGeometry

universe u

namespace ConeQuotient

open GradedCone

open scoped TensorProduct

/-! ### The Hopf algebra structure of `Sym(F)` -/

section Bundle

variable (R : Type u) [CommRing R] (F : Type u) [AddCommGroup F] [Module R F]

/-- The comultiplication of the Hopf algebra `Sym(F)`, that is, the coordinate algebra map of
the addition `E ×_{Spec R} E → E` of the vector bundle `E = Spec Sym(F)`. -/
noncomputable def symComul :
    SymmetricAlgebra R F →ₐ[R] SymmetricAlgebra R F ⊗[R] SymmetricAlgebra R F :=
  SymmetricAlgebra.lift
    ((Algebra.TensorProduct.includeLeft (R := R)
        (A := SymmetricAlgebra R F) (B := SymmetricAlgebra R F)).toLinearMap.comp
        (SymmetricAlgebra.ι R F) +
      (Algebra.TensorProduct.includeRight (R := R)
        (A := SymmetricAlgebra R F) (B := SymmetricAlgebra R F)).toLinearMap.comp
        (SymmetricAlgebra.ι R F))

@[simp]
theorem symComul_ι (m : F) :
    symComul R F (SymmetricAlgebra.ι R F m) =
      SymmetricAlgebra.ι R F m ⊗ₜ[R] 1 + 1 ⊗ₜ[R] SymmetricAlgebra.ι R F m := by
  rw [symComul, SymmetricAlgebra.lift_ι_apply]
  rfl

variable {R F}
variable {F' : Type u} [AddCommGroup F'] [Module R F']

/-- The algebra map `Sym(F) → Sym(F')` induced by a linear map `u : F →ₗ[R] F'`.  On spectra it
is the morphism of vector bundles `Spec Sym(F') → Spec Sym(F)`. -/
noncomputable def symMap (u : F →ₗ[R] F') :
    SymmetricAlgebra R F →ₐ[R] SymmetricAlgebra R F' :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι R F').comp u)

@[simp]
theorem symMap_ι (u : F →ₗ[R] F') (m : F) :
    symMap u (SymmetricAlgebra.ι R F m) = SymmetricAlgebra.ι R F' (u m) :=
  SymmetricAlgebra.lift_ι_apply _ _

variable {B C : Type u} [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]

/-- Post-composition of a `B`-point of a vector bundle with an algebra map. -/
theorem comp_symLift (g : B →ₐ[R] C) (l : F →ₗ[R] B) :
    g.comp (SymmetricAlgebra.lift l) = SymmetricAlgebra.lift (g.toLinearMap.comp l) := by
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
  simp

/-- Pre-composition of a `B`-point of a vector bundle with a morphism of vector bundles. -/
theorem symLift_comp_symMap (u : F →ₗ[R] F') (l : F' →ₗ[R] B) :
    (SymmetricAlgebra.lift l).comp (symMap u) = SymmetricAlgebra.lift (l.comp u) := by
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
  simp

/-- The comultiplication of `Sym(F)` computes the addition of `B`-points of the bundle. -/
theorem lift_comp_symComul (m l : F →ₗ[R] B) :
    (Algebra.TensorProduct.lift (SymmetricAlgebra.lift m) (SymmetricAlgebra.lift l)
        fun _ _ => Commute.all _ _).comp (symComul R F) = SymmetricAlgebra.lift (m + l) := by
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x => ?_)
  simp

end Bundle

/-! ### Actions of a vector bundle on a cone -/

section Action

variable {R S F : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup F] [Module R F]

/-- The `B`-point of `C = Spec S` obtained by translating the `B`-point `φ` by the `B`-point
`l : F →ₗ[R] B` of the vector bundle `E = Spec Sym(F)`, for a coaction `α`. -/
noncomputable def translate (α : S →ₐ[R] S ⊗[R] SymmetricAlgebra R F)
    {B : Type u} [CommRing B] [Algebra R B] (φ : S →ₐ[R] B) (l : F →ₗ[R] B) : S →ₐ[R] B :=
  (Algebra.TensorProduct.lift φ (SymmetricAlgebra.lift l) fun _ _ => Commute.all _ _).comp α

variable {B C : Type u} [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]

/-- Post-composition distributes over the universal map out of a tensor product. -/
theorem comp_tensorLift {S' : Type u} [CommRing S'] [Algebra R S']
    (g : B →ₐ[R] C) (f₁ : S →ₐ[R] B) (f₂ : S' →ₐ[R] B) :
    g.comp (Algebra.TensorProduct.lift f₁ f₂ fun _ _ => Commute.all _ _) =
      Algebra.TensorProduct.lift (g.comp f₁) (g.comp f₂) fun _ _ => Commute.all _ _ := by
  refine tensor_ext ?_ ?_
  · rw [AlgHom.comp_assoc, Algebra.TensorProduct.lift_comp_includeLeft,
      Algebra.TensorProduct.lift_comp_includeLeft]
  · rw [AlgHom.comp_assoc, Algebra.TensorProduct.lift_comp_includeRight',
      Algebra.TensorProduct.lift_comp_includeRight']

/-- The action on points is natural in the test algebra. -/
theorem comp_translate (α : S →ₐ[R] S ⊗[R] SymmetricAlgebra R F) (g : B →ₐ[R] C)
    (φ : S →ₐ[R] B) (l : F →ₗ[R] B) :
    g.comp (translate α φ l) = translate α (g.comp φ) (g.toLinearMap.comp l) := by
  rw [translate, translate, ← AlgHom.comp_assoc, comp_tensorLift, comp_symLift]

/-- The `B`-points of a vector bundle, spelled through its universal property. -/
theorem pointsEquiv_symm_eq (l : F →ₗ[R] B) :
    (pointsEquiv R F B).symm l = SymmetricAlgebra.lift l :=
  rfl

/-- Composing a point with a contraction of the cone is scaling the point. -/
theorem comp_contraction (ψ : S →ₐ[R] Polynomial S) (φ : S →ₐ[R] B) (r : R) :
    φ.comp (contraction ψ r) = scale ψ φ (algebraMap R B r) := by
  rw [contraction, comp_scale, AlgHom.comp_id, AlgHom.commutes]

/-- Scaling a point of the target of a morphism of cones agrees with scaling the composite. -/
theorem scale_comp_of_isConeHom {S' : Type u} [CommRing S'] [Algebra R S']
    {ψ : S →ₐ[R] Polynomial S} {ψ' : S' →ₐ[R] Polynomial S'} {φ₀ : S →ₐ[R] S'}
    (h : IsConeHom ψ ψ' φ₀) (g : S' →ₐ[R] B) (b : B) :
    (scale ψ' g b).comp φ₀ = scale ψ (g.comp φ₀) b := by
  rw [scale, scale, AlgHom.comp_assoc, ← h, ← AlgHom.comp_assoc, evalHom_comp_mapAlgHom]

/-- An action of the affine vector bundle `E = Spec Sym(F)` on the affine cone `C = Spec S`
over `Spec R`, compatible with the two cone structures.

The `Prop` fields are hypotheses about the coaction `act`: they are the unit and associativity
laws of a monoid action on the functor of points, and the requirement that the action map
`C ×_{Spec R} E → C` be a morphism of cones.  They are proved for every action constructed in
this file. -/
structure ConeAction (R : Type u) [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
    (F : Type u) [AddCommGroup F] [Module R F] where
  /-- The `𝔸¹`-contraction coaction exhibiting `Spec S` as a cone over `Spec R`. -/
  coaction : S →ₐ[R] Polynomial S
  /-- The contraction coaction satisfies the counit and coassociativity laws. -/
  isCone : IsConeCoaction coaction
  /-- The coaction of the vector bundle on the coordinate ring of the cone. -/
  act : S →ₐ[R] S ⊗[R] SymmetricAlgebra R F
  /-- Unit law: translating by the zero section does nothing. -/
  act_zero : ∀ {B : Type u} [CommRing B] [Algebra R B] (φ : S →ₐ[R] B),
    translate act φ 0 = φ
  /-- Associativity law: translating twice is translating by the sum. -/
  act_add : ∀ {B : Type u} [CommRing B] [Algebra R B] (φ : S →ₐ[R] B) (l l' : F →ₗ[R] B),
    translate act (translate act φ l) l' = translate act φ (l + l')
  /-- The action map `C ×_{Spec R} E → C` is a morphism of cones. -/
  conic : IsConeHom coaction (tensorCoaction coaction (symCoaction R F)) act

namespace ConeAction

variable (A : ConeAction R S F)

/-- Contractions commute with the action: the action is `𝔾ₘ`-equivariant, where `𝔾ₘ` acts by
the contraction on the cone and by scalar multiplication on the vector bundle. -/
theorem scale_translate (φ : S →ₐ[R] B) (l : F →ₗ[R] B) (b : B) :
    scale A.coaction (translate A.act φ l) b =
      translate A.act (scale A.coaction φ b) (b • l) := by
  set L : (S ⊗[R] SymmetricAlgebra R F) →ₐ[R] B :=
    Algebra.TensorProduct.lift φ (SymmetricAlgebra.lift l) fun _ _ => Commute.all _ _ with hL
  have key : scale (tensorCoaction A.coaction (symCoaction R F)) L b =
      Algebra.TensorProduct.lift (scale A.coaction φ b) (SymmetricAlgebra.lift (b • l))
        fun _ _ => Commute.all _ _ := by
    refine tensor_ext ?_ ?_
    · rw [scale_comp_of_isConeHom (isConeHom_includeLeft A.coaction (symCoaction R F)),
        Algebra.TensorProduct.lift_comp_includeLeft,
        Algebra.TensorProduct.lift_comp_includeLeft]
    · rw [scale_comp_of_isConeHom (isConeHom_includeRight A.coaction (symCoaction R F)),
        Algebra.TensorProduct.lift_comp_includeRight',
        Algebra.TensorProduct.lift_comp_includeRight', ← pointsEquiv_symm_eq,
        ← pointsEquiv_symm_eq, scale_symCoaction]
  calc scale A.coaction (translate A.act φ l) b
      = (evalHom (L.comp A.act) b).comp A.coaction := rfl
    _ = (evalHom L b).comp ((Polynomial.mapAlgHom A.act).comp A.coaction) := by
        rw [← AlgHom.comp_assoc, evalHom_comp_mapAlgHom]
    _ = (scale (tensorCoaction A.coaction (symCoaction R F)) L b).comp A.act := by
        rw [A.conic, scale, ← AlgHom.comp_assoc]
    _ = translate A.act (scale A.coaction φ b) (b • l) := by rw [key]; rfl

/-- Contracting any point of the cone by `0` gives the vertex. -/
theorem scale_zero_eq {ε : S →ₐ[R] R} (hv : IsConeVertex A.coaction ε) (φ : S →ₐ[R] B) :
    scale A.coaction φ (0 : B) = (Algebra.ofId R B).comp ε := by
  have h0 : φ.comp (contraction A.coaction (0 : R)) = scale A.coaction φ (0 : B) := by
    rw [comp_contraction, map_zero]
  rw [← h0, hv, ← AlgHom.comp_assoc]
  congr 1
  exact AlgHom.ext fun r => φ.commutes r

/-- The vertex of the cone is a fixed point of every contraction, over every test algebra. -/
theorem scale_vertex {ε : S →ₐ[R] R} (hv : IsConeVertex A.coaction ε) (b : B) :
    scale A.coaction ((Algebra.ofId R B).comp ε) b = (Algebra.ofId R B).comp ε := by
  have h := A.scale_zero_eq hv ((Algebra.ofId R B).comp ε)
  calc scale A.coaction ((Algebra.ofId R B).comp ε) b
      = scale A.coaction (scale A.coaction ((Algebra.ofId R B).comp ε) (0 : B)) b := by rw [h]
    _ = scale A.coaction ((Algebra.ofId R B).comp ε) (0 * b) := A.isCone.scale_scale _ 0 b
    _ = (Algebra.ofId R B).comp ε := by rw [zero_mul, h]

/-- Contracting a translated point by a scalar of the base. -/
theorem comp_contraction_translate (r : R) (φ : S →ₐ[R] B) (l : F →ₗ[R] B) :
    (translate A.act φ l).comp (contraction A.coaction r) =
      translate A.act (φ.comp (contraction A.coaction r)) (algebraMap R B r • l) := by
  rw [comp_contraction, comp_contraction, A.scale_translate]

end ConeAction

end Action

/-! ### The quotient groupoid `[C/E]` -/

section Quotients

variable {R S F : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup F] [Module R F]

/-- The `B`-points of the quotient `[C/E]`: the action groupoid whose objects are the
`B`-points of the cone `C` and whose arrows are the `B`-points of the bundle `E` translating
one into the other. -/
@[ext]
structure QuotientGroupoid (A : ConeAction R S F) (B : Type u) [CommRing B] [Algebra R B] where
  /-- The `B`-point of the cone underlying an object of the quotient groupoid. -/
  point : S →ₐ[R] B

namespace QuotientGroupoid

variable {A : ConeAction R S F} {B C : Type u} [CommRing B] [Algebra R B]
  [CommRing C] [Algebra R C]

/-- The projection `C → [C/E]` on `B`-points: it is a bijection on objects. -/
def of (A : ConeAction R S F) (x : S →ₐ[R] B) : QuotientGroupoid A B := ⟨x⟩

@[simp]
theorem point_of (A : ConeAction R S F) (x : S →ₐ[R] B) : (of A x).point = x :=
  rfl

/-- An arrow of the quotient groupoid: a `B`-point of the vector bundle carrying the source
to the target. -/
@[ext]
structure Hom (x y : QuotientGroupoid A B) where
  /-- The translating `B`-point of the vector bundle. -/
  val : F →ₗ[R] B
  /-- The translation carries the source to the target. -/
  translate_eq : translate A.act x.point val = y.point

/-- The action groupoid structure on the `B`-points of `[C/E]`. -/
instance instCategory : Category (QuotientGroupoid A B) where
  Hom := Hom
  id x := ⟨0, A.act_zero x.point⟩
  comp f g := ⟨f.val + g.val, by
    rw [← A.act_add, f.translate_eq, g.translate_eq]⟩
  id_comp f := Hom.ext (zero_add _)
  comp_id f := Hom.ext (add_zero _)
  assoc f g h := Hom.ext (add_assoc _ _ _)

@[simp]
theorem id_val (x : QuotientGroupoid A B) : (𝟙 x : x ⟶ x).val = 0 :=
  rfl

@[simp]
theorem comp_val {x y z : QuotientGroupoid A B} (f : x ⟶ y) (g : y ⟶ z) :
    (f ≫ g).val = f.val + g.val :=
  rfl

/-- Every arrow of the action groupoid is invertible. -/
instance instGroupoid : Groupoid (QuotientGroupoid A B) where
  inv f := ⟨-f.val, by
    rw [← f.translate_eq, A.act_add, add_neg_cancel, A.act_zero]⟩
  inv_comp f := Hom.ext (neg_add_cancel _)
  comp_inv f := Hom.ext (add_neg_cancel _)

@[simp]
theorem inv_val {x y : QuotientGroupoid A B} (f : x ⟶ y) :
    (Groupoid.inv f).val = -f.val :=
  rfl

/-- An equality of objects of the quotient groupoid is witnessed by the zero translation. -/
@[simp]
theorem eqToHom_val {x y : QuotientGroupoid A B} (h : x = y) :
    (eqToHom h : x ⟶ y).val = 0 := by
  subst h
  rfl

/-- Arrows out of an object of the quotient groupoid are exactly the `B`-points of the bundle
translating it into the target. -/
def homEquiv (x y : QuotientGroupoid A B) :
    (x ⟶ y) ≃ {l : F →ₗ[R] B // translate A.act x.point l = y.point} where
  toFun f := ⟨f.val, f.translate_eq⟩
  invFun l := ⟨l.1, l.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Two objects of the quotient groupoid are isomorphic exactly when they lie in the same
orbit of the action on points. -/
theorem nonempty_hom_iff (x y : QuotientGroupoid A B) :
    Nonempty (x ⟶ y) ↔ ∃ l : F →ₗ[R] B, translate A.act x.point l = y.point :=
  ⟨fun ⟨f⟩ => ⟨f.val, f.translate_eq⟩, fun ⟨l, hl⟩ => ⟨⟨l, hl⟩⟩⟩

/-- The canonical isomorphism between a point and its translate. -/
noncomputable def isoTranslate (x : QuotientGroupoid A B) (l : F →ₗ[R] B) :
    x ≅ of A (translate A.act x.point l) :=
  (Groupoid.isoEquivHom _ _).symm ⟨l, rfl⟩

/-- Automorphisms of an object of the quotient groupoid are the stabiliser of the corresponding
point of the cone: there is no hidden collapsing or enlarging of stabilisers. -/
def autEquivStabilizer (x : QuotientGroupoid A B) :
    (x ⟶ x) ≃ {l : F →ₗ[R] B // translate A.act x.point l = x.point} :=
  homEquiv x x

/-! #### The contraction action on the quotient -/

/-- The contraction of the quotient groupoid `[C/E](B)` by a scalar `b : B`.  It is
well defined because the action is `𝔾ₘ`-equivariant. -/
noncomputable def contractionFunctor (A : ConeAction R S F) (B : Type u) [CommRing B]
    [Algebra R B] (b : B) : QuotientGroupoid A B ⥤ QuotientGroupoid A B where
  obj x := ⟨scale A.coaction x.point b⟩
  map f := ⟨b • f.val,
    (A.scale_translate _ _ _).symm.trans
      (congrArg (fun z => scale A.coaction z b) f.translate_eq)⟩
  map_id _ := Hom.ext (smul_zero b)
  map_comp _ _ := Hom.ext (smul_add b _ _)

@[simp]
theorem contractionFunctor_obj_point (A : ConeAction R S F) (b : B) (x : QuotientGroupoid A B) :
    ((contractionFunctor A B b).obj x).point = scale A.coaction x.point b :=
  rfl

@[simp]
theorem contractionFunctor_map_val (A : ConeAction R S F) (b : B)
    {x y : QuotientGroupoid A B} (f : x ⟶ y) :
    ((contractionFunctor A B b).map f).val = b • f.val :=
  rfl

/-- Contracting the quotient by `1` is the identity. -/
noncomputable def contractionOneIso (A : ConeAction R S F) (B : Type u) [CommRing B]
    [Algebra R B] : contractionFunctor A B 1 ≅ 𝟭 (QuotientGroupoid A B) :=
  NatIso.ofComponents
    (fun x => eqToIso (QuotientGroupoid.ext (A.isCone.scale_one x.point)))
    (fun f => Hom.ext (by simp))

/-- Contracting the quotient by a product is contracting twice. -/
noncomputable def contractionMulIso (A : ConeAction R S F) (B : Type u) [CommRing B]
    [Algebra R B] (b c : B) :
    contractionFunctor A B (b * c) ≅ contractionFunctor A B b ⋙ contractionFunctor A B c :=
  NatIso.ofComponents
    (fun x => eqToIso (QuotientGroupoid.ext (A.isCone.scale_scale x.point b c).symm))
    (fun f => Hom.ext (by simp [mul_comm b c, mul_smul]))

/-- The vertex of the quotient `[C/E]`: the image of the vertex of the cone. -/
def vertexPoint (A : ConeAction R S F) (ε : S →ₐ[R] R) (B : Type u) [CommRing B]
    [Algebra R B] : QuotientGroupoid A B :=
  ⟨(Algebra.ofId R B).comp ε⟩

/-- Contracting the quotient by `0` is the constant functor at the vertex. -/
noncomputable def contractionZeroIso (A : ConeAction R S F) {ε : S →ₐ[R] R}
    (hv : IsConeVertex A.coaction ε) (B : Type u) [CommRing B] [Algebra R B] :
    contractionFunctor A B 0 ≅
      (Functor.const (QuotientGroupoid A B)).obj (vertexPoint A ε B) :=
  NatIso.ofComponents
    (fun x => eqToIso (QuotientGroupoid.ext (A.scale_zero_eq hv x.point)))
    (fun f => Hom.ext (by simp))

/-- The vertex of the quotient is fixed by every contraction. -/
theorem contractionFunctor_vertexPoint (A : ConeAction R S F) {ε : S →ₐ[R] R}
    (hv : IsConeVertex A.coaction ε) (b : B) :
    (contractionFunctor A B b).obj (vertexPoint A ε B) = vertexPoint A ε B :=
  QuotientGroupoid.ext (A.scale_vertex hv b)

/-! #### Reindexing along a map of test algebras -/

/-- Reindexing the quotient groupoid along a map of test algebras: cone actions commute with
change of test scheme. -/
noncomputable def mapQuotient (A : ConeAction R S F) (g : B →ₐ[R] C) :
    QuotientGroupoid A B ⥤ QuotientGroupoid A C where
  obj x := ⟨g.comp x.point⟩
  map f := ⟨g.toLinearMap.comp f.val,
    (comp_translate A.act g _ _).symm.trans (congrArg (fun z => g.comp z) f.translate_eq)⟩
  map_id x := Hom.ext (by ext m; simp)
  map_comp f h := Hom.ext (by ext m; simp)

@[simp]
theorem mapQuotient_obj_point (A : ConeAction R S F) (g : B →ₐ[R] C)
    (x : QuotientGroupoid A B) : ((mapQuotient A g).obj x).point = g.comp x.point :=
  rfl

@[simp]
theorem mapQuotient_map_val (A : ConeAction R S F) (g : B →ₐ[R] C)
    {x y : QuotientGroupoid A B} (f : x ⟶ y) :
    ((mapQuotient A g).map f).val = g.toLinearMap.comp f.val :=
  rfl

/-- Reindexing along the identity is the identity, strictly. -/
theorem mapQuotient_id (A : ConeAction R S F) (B : Type u) [CommRing B] [Algebra R B] :
    mapQuotient A (AlgHom.id R B) = 𝟭 (QuotientGroupoid A B) := by
  refine CategoryTheory.Functor.ext
    (fun x => QuotientGroupoid.ext (AlgHom.id_comp _)) fun x y f => ?_
  refine Hom.ext ?_
  ext m
  simp

/-- Reindexing is strictly functorial in the test algebra. -/
theorem mapQuotient_comp (A : ConeAction R S F) {D : Type u} [CommRing D] [Algebra R D]
    (g : B →ₐ[R] C) (h : C →ₐ[R] D) :
    mapQuotient A (h.comp g) = mapQuotient A g ⋙ mapQuotient A h := by
  refine CategoryTheory.Functor.ext
    (fun x => QuotientGroupoid.ext (AlgHom.comp_assoc _ _ _)) fun x y f => ?_
  refine Hom.ext ?_
  ext m
  simp

/-- Contraction commutes with reindexing along a map of test algebras. -/
theorem mapQuotient_comp_contractionFunctor (A : ConeAction R S F) (g : B →ₐ[R] C) (b : B) :
    contractionFunctor A B b ⋙ mapQuotient A g =
      mapQuotient A g ⋙ contractionFunctor A C (g b) := by
  refine CategoryTheory.Functor.ext (fun x => QuotientGroupoid.ext ?_) fun x y f => ?_
  · exact comp_scale A.coaction g x.point b
  · refine Hom.ext ?_
    ext m
    simp

end QuotientGroupoid

/-- The quotient prestack of `[C/E]` on affine test schemes: the strictly functorial assignment
sending an `R`-algebra `B` to the quotient groupoid `[C/E](B)`. -/
noncomputable def quotientPrestack (A : ConeAction R S F) : CommAlgCat.{u} R ⥤ Cat.{u, u} where
  obj B := Cat.of (QuotientGroupoid A B)
  map g := Functor.toCatHom (QuotientGroupoid.mapQuotient A g.hom)
  map_id B := Cat.ext (QuotientGroupoid.mapQuotient_id A B)
  map_comp g h := Cat.ext (QuotientGroupoid.mapQuotient_comp A g.hom h.hom)

end Quotients

/-! ### The translation action of a vector bundle on itself -/

section Translation

variable {R F : Type u} [CommRing R] [AddCommGroup F] [Module R F]
variable {B : Type u} [CommRing B] [Algebra R B]

/-- The tensor coaction of a product of cones, computed on a pure tensor. -/
theorem tensorCoaction_tmul {S S' : Type u} [CommRing S] [Algebra R S] [CommRing S']
    [Algebra R S'] (ψ : S →ₐ[R] Polynomial S) (ψ' : S' →ₐ[R] Polynomial S') (a : S) (b : S') :
    tensorCoaction ψ ψ' (a ⊗ₜ[R] b) =
      Polynomial.mapAlgHom
          (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S') (ψ a) *
        Polynomial.mapAlgHom
          (Algebra.TensorProduct.includeRight : S' →ₐ[R] S ⊗[R] S') (ψ' b) :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

/-- Translating the `B`-point `m` of the bundle by the `B`-point `l` adds them. -/
theorem translate_symComul_lift (m l : F →ₗ[R] B) :
    translate (symComul R F) (SymmetricAlgebra.lift m) l = SymmetricAlgebra.lift (m + l) :=
  lift_comp_symComul m l

/-- The translation action on `B`-points of a vector bundle is the addition of linear maps. -/
theorem translate_symComul (φ : SymmetricAlgebra R F →ₐ[R] B) (l : F →ₗ[R] B) :
    translate (symComul R F) φ l = SymmetricAlgebra.lift (SymmetricAlgebra.lift.symm φ + l) := by
  conv_lhs => rw [← SymmetricAlgebra.lift.apply_symm_apply φ]
  exact translate_symComul_lift _ _

/-- The translation action of the vector bundle `E = Spec Sym(F)` on itself, coming from the
Hopf-algebra comultiplication of `Sym(F)`. -/
noncomputable def translationAction (R : Type u) [CommRing R] (F : Type u) [AddCommGroup F]
    [Module R F] : ConeAction R (SymmetricAlgebra R F) F where
  coaction := symCoaction R F
  isCone := isConeCoaction_symCoaction R F
  act := symComul R F
  act_zero := by
    intro B _ _ φ
    rw [translate_symComul, add_zero, SymmetricAlgebra.lift.apply_symm_apply]
  act_add := by
    intro B _ _ φ l l'
    rw [translate_symComul, translate_symComul, translate_symComul,
      SymmetricAlgebra.lift.symm_apply_apply, add_assoc]
  conic := by
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => ?_)
    have hL : Polynomial.mapAlgHom (symComul R F) (symCoaction R F (SymmetricAlgebra.ι R F m)) =
        Polynomial.C (symComul R F (SymmetricAlgebra.ι R F m)) * Polynomial.X := by
      rw [symCoaction_ι, map_mul]
      simp
    have hR : tensorCoaction (symCoaction R F) (symCoaction R F)
          (symComul R F (SymmetricAlgebra.ι R F m)) =
        Polynomial.C (symComul R F (SymmetricAlgebra.ι R F m)) * Polynomial.X := by
      rw [symComul_ι, map_add, tensorCoaction_tmul, tensorCoaction_tmul, symCoaction_ι,
        map_one]
      simp [add_mul]
    exact hL.trans hR.symm

/-- Between any two `B`-points of a vector bundle there is exactly one translation carrying the
first to the second: the translation action is simply transitive. -/
theorem translationAction_hom_unique (x y : QuotientGroupoid (translationAction R F) B) :
    ∃! l : F →ₗ[R] B, translate (translationAction R F).act x.point l = y.point := by
  refine ⟨SymmetricAlgebra.lift.symm y.point - SymmetricAlgebra.lift.symm x.point, ?_, ?_⟩
  · change translate (symComul R F) x.point _ = y.point
    rw [translate_symComul, add_sub_cancel, SymmetricAlgebra.lift.apply_symm_apply]
  · intro l hl
    have hl' : translate (symComul R F) x.point l = y.point := hl
    rw [translate_symComul] at hl'
    have h2 := congrArg SymmetricAlgebra.lift.symm hl'
    rw [SymmetricAlgebra.lift.symm_apply_apply] at h2
    rw [← h2]
    abel

/-- The quotient groupoid of a vector bundle by its own translation action has at most one
arrow between any two objects: the stabilisers are trivial. -/
instance translationHom_subsingleton (x y : QuotientGroupoid (translationAction R F) B) :
    Subsingleton (x ⟶ y) where
  allEq f g := QuotientGroupoid.Hom.ext
    ((translationAction_hom_unique x y).unique f.translate_eq g.translate_eq)

/-- The unique arrow between two objects of the quotient of a vector bundle by its own
translation action. -/
noncomputable def translationHom (x y : QuotientGroupoid (translationAction R F) B) : x ⟶ y :=
  ⟨(translationAction_hom_unique x y).choose,
    (translationAction_hom_unique x y).choose_spec.1⟩

/-- The quotient of a vector bundle by its own translation action is the punctual groupoid:
`[E/E] ≃ Spec R`.  This is the affine shadow of the fact that the quotient of a scheme by a
free transitive group action is the base. -/
noncomputable def translationQuotientEquivalence (R : Type u) [CommRing R] (F : Type u)
    [AddCommGroup F] [Module R F] (B : Type u) [CommRing B] [Algebra R B] :
    QuotientGroupoid (translationAction R F) B ≌ Discrete PUnit.{u + 1} where
  functor :=
    { obj := fun _ => ⟨PUnit.unit⟩
      map := fun _ => 𝟙 _ }
  inverse :=
    { obj := fun _ => ⟨(Algebra.ofId R B).comp SymmetricAlgebra.algebraMapInv⟩
      map := fun _ => 𝟙 _ }
  unitIso := NatIso.ofComponents
    (fun x => (Groupoid.isoEquivHom _ _).symm (translationHom x _))
    (fun _ => Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _)

end Translation

/-! ### Equivariant morphisms and homotopies -/

section Equivariant

variable {R S S' S'' F F' F'' : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [CommRing S'] [Algebra R S'] [CommRing S''] [Algebra R S'']
  [AddCommGroup F] [Module R F] [AddCommGroup F'] [Module R F']
  [AddCommGroup F''] [Module R F'']
variable {B C : Type u} [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]

/-- An equivariant morphism from the cone with action `(C', E')` to the cone with action
`(C, E)`: the algebra map `φ : S →ₐ[R] S'` is the morphism of cones `C' → C`, and the linear map
`u : F →ₗ[R] F'` induces the morphism of vector bundles `E' → E`. -/
def IsEquivariant (A : ConeAction R S F) (A' : ConeAction R S' F')
    (φ : S →ₐ[R] S') (u : F →ₗ[R] F') : Prop :=
  (Algebra.TensorProduct.map φ (symMap u)).comp A.act = A'.act.comp φ

variable {A : ConeAction R S F} {A' : ConeAction R S' F'} {A'' : ConeAction R S'' F''}
  {φ : S →ₐ[R] S'} {u : F →ₗ[R] F'}

/-- An equivariant morphism intertwines the two actions on points. -/
theorem translate_comp (h : IsEquivariant A A' φ u) (x : S' →ₐ[R] B) (l : F' →ₗ[R] B) :
    (translate A'.act x l).comp φ = translate A.act (x.comp φ) (l.comp u) := by
  have key : (Algebra.TensorProduct.lift x (SymmetricAlgebra.lift l)
        fun _ _ => Commute.all _ _).comp (Algebra.TensorProduct.map φ (symMap u)) =
      Algebra.TensorProduct.lift (x.comp φ) (SymmetricAlgebra.lift (l.comp u))
        fun _ _ => Commute.all _ _ := by
    refine tensor_ext ?_ ?_
    · rw [AlgHom.comp_assoc, Algebra.TensorProduct.map_comp_includeLeft, ← AlgHom.comp_assoc,
        Algebra.TensorProduct.lift_comp_includeLeft,
        Algebra.TensorProduct.lift_comp_includeLeft]
    · rw [AlgHom.comp_assoc, Algebra.TensorProduct.map_comp_includeRight, ← AlgHom.comp_assoc,
        Algebra.TensorProduct.lift_comp_includeRight',
        Algebra.TensorProduct.lift_comp_includeRight', symLift_comp_symMap]
  rw [translate, translate, AlgHom.comp_assoc, ← h, ← AlgHom.comp_assoc, key]

/-- The identity is an equivariant morphism. -/
theorem isEquivariant_id (A : ConeAction R S F) :
    IsEquivariant A A (AlgHom.id R S) (LinearMap.id) := by
  have hs : symMap (LinearMap.id : F →ₗ[R] F) = AlgHom.id R (SymmetricAlgebra R F) := by
    rw [symMap, LinearMap.comp_id, SymmetricAlgebra.lift_ι]
  rw [IsEquivariant, hs, Algebra.TensorProduct.map_id, AlgHom.id_comp, AlgHom.comp_id]

/-- Equivariant morphisms compose. -/
theorem IsEquivariant.comp {φ' : S' →ₐ[R] S''} {u' : F' →ₗ[R] F''}
    (h : IsEquivariant A A' φ u) (h' : IsEquivariant A' A'' φ' u') :
    IsEquivariant A A'' (φ'.comp φ) (u'.comp u) := by
  have hs : symMap (u'.comp u) = (symMap u').comp (symMap u) := by
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => ?_)
    simp
  rw [IsEquivariant, hs, Algebra.TensorProduct.map_comp, AlgHom.comp_assoc, h,
    ← AlgHom.comp_assoc, h', AlgHom.comp_assoc]

/-- The functor `[C'/E'] → [C/E]` induced on quotient groupoids by an equivariant morphism. -/
noncomputable def quotientFunctor (h : IsEquivariant A A' φ u) (B : Type u) [CommRing B]
    [Algebra R B] : QuotientGroupoid A' B ⥤ QuotientGroupoid A B where
  obj x := ⟨x.point.comp φ⟩
  map f := ⟨f.val.comp u,
    (translate_comp h _ _).symm.trans (congrArg (fun z => z.comp φ) f.translate_eq)⟩
  map_id _ := QuotientGroupoid.Hom.ext (LinearMap.zero_comp u)
  map_comp f g := QuotientGroupoid.Hom.ext (by ext m; simp)

@[simp]
theorem quotientFunctor_obj_point (h : IsEquivariant A A' φ u) (x : QuotientGroupoid A' B) :
    ((quotientFunctor h B).obj x).point = x.point.comp φ :=
  rfl

@[simp]
theorem quotientFunctor_map_val (h : IsEquivariant A A' φ u)
    {x y : QuotientGroupoid A' B} (f : x ⟶ y) :
    ((quotientFunctor h B).map f).val = f.val.comp u :=
  rfl

/-- The quotient of the identity equivariant morphism is the identity functor. -/
theorem quotientFunctor_id (A : ConeAction R S F) (B : Type u) [CommRing B] [Algebra R B] :
    quotientFunctor (isEquivariant_id A) B = 𝟭 (QuotientGroupoid A B) := by
  refine CategoryTheory.Functor.ext
    (fun x => QuotientGroupoid.ext (AlgHom.comp_id _)) fun x y f => ?_
  refine QuotientGroupoid.Hom.ext ?_
  ext m
  simp

/-- The quotient functor is strictly compatible with composition of equivariant morphisms. -/
theorem quotientFunctor_comp {φ' : S' →ₐ[R] S''} {u' : F' →ₗ[R] F''}
    (h : IsEquivariant A A' φ u) (h' : IsEquivariant A' A'' φ' u')
    (B : Type u) [CommRing B] [Algebra R B] :
    quotientFunctor (h.comp h') B = quotientFunctor h' B ⋙ quotientFunctor h B := by
  refine CategoryTheory.Functor.ext
    (fun x => QuotientGroupoid.ext (AlgHom.comp_assoc _ _ _).symm) fun x y f => ?_
  refine QuotientGroupoid.Hom.ext ?_
  ext m
  simp

/-- The functor induced by an equivariant morphism commutes with reindexing along a map of
test algebras. -/
theorem quotientFunctor_comp_mapQuotient (h : IsEquivariant A A' φ u) (g : B →ₐ[R] C) :
    quotientFunctor h B ⋙ QuotientGroupoid.mapQuotient A g =
      QuotientGroupoid.mapQuotient A' g ⋙ quotientFunctor h C := by
  refine CategoryTheory.Functor.ext
    (fun x => QuotientGroupoid.ext (AlgHom.comp_assoc _ _ _)) fun x y f => ?_
  refine QuotientGroupoid.Hom.ext ?_
  ext m
  simp

/-- A homotopy between two equivariant morphisms `(φ₁, u₁)` and `(φ₂, u₂)` from `(C', E')` to
`(C, E)`: a morphism `H : C' → E`, that is an `S'`-point `val` of the vector bundle `E`,
translating `φ₁` to `φ₂`, and whose failure to be invariant under the action of `E'` is exactly
the difference of the two bundle maps. -/
structure Homotopy (A : ConeAction R S F) (A' : ConeAction R S' F')
    (φ₁ φ₂ : S →ₐ[R] S') (u₁ u₂ : F →ₗ[R] F') where
  /-- The morphism `C' → E` realising the homotopy. -/
  val : F →ₗ[R] S'
  /-- The homotopy carries the first morphism to the second. -/
  translate_eq : translate A.act φ₁ val = φ₂
  /-- Compatibility of the homotopy with the action of `E'`. -/
  compat : ∀ {B : Type u} [CommRing B] [Algebra R B] (x : S' →ₐ[R] B) (l : F' →ₗ[R] B),
    (translate A'.act x l).toLinearMap.comp val =
      x.toLinearMap.comp val + l.comp (u₂ - u₁)

namespace Homotopy

variable {φ₁ φ₂ : S →ₐ[R] S'} {u₁ u₂ : F →ₗ[R] F'}

/-- The `2`-cell of quotient groupoids determined by a homotopy of equivariant morphisms. -/
noncomputable def natIso (H : Homotopy A A' φ₁ φ₂ u₁ u₂) (h₁ : IsEquivariant A A' φ₁ u₁)
    (h₂ : IsEquivariant A A' φ₂ u₂) (B : Type u) [CommRing B] [Algebra R B] :
    quotientFunctor h₁ B ≅ quotientFunctor h₂ B :=
  NatIso.ofComponents
    (fun x => (Groupoid.isoEquivHom _ _).symm
      ⟨x.point.toLinearMap.comp H.val,
        (comp_translate A.act x.point φ₁ H.val).symm.trans
          (congrArg (fun z => x.point.comp z) H.translate_eq)⟩)
    (fun {x y} f => QuotientGroupoid.Hom.ext (by
      have hc := H.compat (A' := A') x.point f.val
      rw [f.translate_eq] at hc
      simp only [QuotientGroupoid.comp_val, quotientFunctor_map_val,
        Groupoid.isoEquivHom_symm_apply_hom, hc, LinearMap.comp_sub]
      abel))

end Homotopy

/-! ### The criterion for equivalent quotient presentations -/

/-- Criterion for a morphism of quotient presentations to induce an equivalence of quotient
groupoids.  The first hypothesis says that every point of `C` lies in the image of `C'` up to
the action of `E`, the second that the translations of a given pair of points of `C'` are
detected injectively by `E`, and the third that every translation in `E` between images comes
from a translation in `E'`.  Nothing here is stored as presentation data: the conclusion is an
honest theorem about the constructed quotient groupoids. -/
theorem isEquivalence_quotientFunctor (h : IsEquivariant A A' φ u) (B : Type u) [CommRing B]
    [Algebra R B]
    (hsurj : ∀ y : S →ₐ[R] B, ∃ x : S' →ₐ[R] B, ∃ l : F →ₗ[R] B,
      translate A.act (x.comp φ) l = y)
    (hinj : ∀ (x y : S' →ₐ[R] B) (l₁ l₂ : F' →ₗ[R] B), translate A'.act x l₁ = y →
      translate A'.act x l₂ = y → l₁.comp u = l₂.comp u → l₁ = l₂)
    (hlift : ∀ (x y : S' →ₐ[R] B) (l : F →ₗ[R] B),
      translate A.act (x.comp φ) l = y.comp φ →
      ∃ l' : F' →ₗ[R] B, translate A'.act x l' = y ∧ l'.comp u = l) :
    (quotientFunctor h B).IsEquivalence where
  faithful :=
    ⟨fun {x y} f g hfg => QuotientGroupoid.Hom.ext
      (hinj x.point y.point f.val g.val f.translate_eq g.translate_eq
        (congrArg QuotientGroupoid.Hom.val hfg))⟩
  full :=
    ⟨fun {x y} k => by
      obtain ⟨l', hl', hu⟩ := hlift x.point y.point k.val k.translate_eq
      exact ⟨⟨l', hl'⟩, QuotientGroupoid.Hom.ext hu⟩⟩
  essSurj :=
    ⟨fun y => by
      obtain ⟨x, l, hl⟩ := hsurj y.point
      exact ⟨⟨x⟩, ⟨(Groupoid.isoEquivHom _ _).symm ⟨l, hl⟩⟩⟩⟩

end Equivariant

/-! ### The free action of a vector bundle on a product -/

section FreeAction

variable {R S F : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup F] [Module R F]
variable {B : Type u} [CommRing B] [Algebra R B]

/-- A map out of a product of cones is a morphism of cones as soon as its two restrictions
are. -/
theorem isConeHom_tensor_ext {S' S'' : Type u} [CommRing S'] [Algebra R S']
    [CommRing S''] [Algebra R S''] {ψ : S →ₐ[R] Polynomial S} {ψ' : S' →ₐ[R] Polynomial S'}
    {ψ'' : S'' →ₐ[R] Polynomial S''} {α : (S ⊗[R] S') →ₐ[R] S''}
    (hL : IsConeHom ψ ψ''
      (α.comp (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] S')))
    (hR : IsConeHom ψ' ψ''
      (α.comp (Algebra.TensorProduct.includeRight : S' →ₐ[R] S ⊗[R] S'))) :
    IsConeHom (tensorCoaction ψ ψ') ψ'' α := by
  refine tensor_ext ?_ ?_
  · rw [AlgHom.comp_assoc, ← isConeHom_includeLeft ψ ψ', ← AlgHom.comp_assoc, mapAlgHom_comp,
      hL, AlgHom.comp_assoc]
  · rw [AlgHom.comp_assoc, ← isConeHom_includeRight ψ ψ', ← AlgHom.comp_assoc, mapAlgHom_comp,
      hR, AlgHom.comp_assoc]

variable (R S F) in
/-- The component of the free action on the cone factor of `C ×_{Spec R} E`. -/
noncomputable def freeLeft :
    S →ₐ[R] (S ⊗[R] SymmetricAlgebra R F) ⊗[R] SymmetricAlgebra R F :=
  (Algebra.TensorProduct.includeLeft :
      (S ⊗[R] SymmetricAlgebra R F) →ₐ[R]
        (S ⊗[R] SymmetricAlgebra R F) ⊗[R] SymmetricAlgebra R F).comp
    (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] SymmetricAlgebra R F)

variable (R S F) in
/-- The component of the free action on the bundle factor of `C ×_{Spec R} E`: it is the
comultiplication of `Sym(F)`. -/
noncomputable def freeRight :
    SymmetricAlgebra R F →ₐ[R]
      (S ⊗[R] SymmetricAlgebra R F) ⊗[R] SymmetricAlgebra R F :=
  (Algebra.TensorProduct.map
      (Algebra.TensorProduct.includeRight :
        SymmetricAlgebra R F →ₐ[R] S ⊗[R] SymmetricAlgebra R F)
      (AlgHom.id R (SymmetricAlgebra R F))).comp (symComul R F)

variable (R S F) in
/-- The coaction of `E = Spec Sym(F)` on the product `C ×_{Spec R} E` by translation on the
second factor.  On points it is `(x, v) ↦ (x, v + l)`, so the action is free. -/
noncomputable def freeCoaction :
    (S ⊗[R] SymmetricAlgebra R F) →ₐ[R]
      (S ⊗[R] SymmetricAlgebra R F) ⊗[R] SymmetricAlgebra R F :=
  Algebra.TensorProduct.lift (freeLeft R S F) (freeRight R S F)
    (fun x y => Commute.all (freeLeft R S F x) (freeRight R S F y))

theorem freeCoaction_comp_includeLeft :
    (freeCoaction R S F).comp
        (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] SymmetricAlgebra R F) =
      (Algebra.TensorProduct.includeLeft :
          (S ⊗[R] SymmetricAlgebra R F) →ₐ[R] _).comp
        (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] SymmetricAlgebra R F) := by
  simp only [freeCoaction, Algebra.TensorProduct.lift_comp_includeLeft, freeLeft]

theorem freeCoaction_comp_includeRight :
    (freeCoaction R S F).comp
        (Algebra.TensorProduct.includeRight :
          SymmetricAlgebra R F →ₐ[R] S ⊗[R] SymmetricAlgebra R F) =
      (Algebra.TensorProduct.map
        (Algebra.TensorProduct.includeRight :
          SymmetricAlgebra R F →ₐ[R] S ⊗[R] SymmetricAlgebra R F)
        (AlgHom.id R (SymmetricAlgebra R F))).comp (symComul R F) := by
  simp only [freeCoaction, Algebra.TensorProduct.lift_comp_includeRight', freeRight]

/-- Every `B`-point of a product `C ×_{Spec R} E` is a pair consisting of a `B`-point of `C`
and a `B`-point of `E`. -/
theorem tensorPoint_eq (Φ : (S ⊗[R] SymmetricAlgebra R F) →ₐ[R] B) :
    Φ = Algebra.TensorProduct.lift (Φ.comp Algebra.TensorProduct.includeLeft)
      (SymmetricAlgebra.lift
        (SymmetricAlgebra.lift.symm (Φ.comp Algebra.TensorProduct.includeRight)))
      (fun _ _ => Commute.all _ _) := by
  rw [SymmetricAlgebra.lift.apply_symm_apply]
  refine tensor_ext ?_ ?_
  · rw [Algebra.TensorProduct.lift_comp_includeLeft]
  · rw [Algebra.TensorProduct.lift_comp_includeRight']

/-- The free action adds the translating point to the bundle component of a point. -/
theorem translate_freeCoaction (x : S →ₐ[R] B) (v l : F →ₗ[R] B) :
    translate (freeCoaction R S F)
        (Algebra.TensorProduct.lift x (SymmetricAlgebra.lift v)
          fun _ _ => Commute.all _ _) l =
      Algebra.TensorProduct.lift x (SymmetricAlgebra.lift (v + l))
        fun _ _ => Commute.all _ _ := by
  refine tensor_ext ?_ ?_
  · rw [translate, AlgHom.comp_assoc, freeCoaction_comp_includeLeft, ← AlgHom.comp_assoc,
      Algebra.TensorProduct.lift_comp_includeLeft,
      Algebra.TensorProduct.lift_comp_includeLeft,
      Algebra.TensorProduct.lift_comp_includeLeft]
  · rw [translate, AlgHom.comp_assoc, freeCoaction_comp_includeRight, ← AlgHom.comp_assoc,
      Algebra.TensorProduct.lift_comp_includeRight']
    have key : (Algebra.TensorProduct.lift
          (Algebra.TensorProduct.lift x (SymmetricAlgebra.lift v)
            fun _ _ => Commute.all _ _) (SymmetricAlgebra.lift l)
            fun _ _ => Commute.all _ _).comp
          (Algebra.TensorProduct.map
            (Algebra.TensorProduct.includeRight :
              SymmetricAlgebra R F →ₐ[R] S ⊗[R] SymmetricAlgebra R F)
            (AlgHom.id R (SymmetricAlgebra R F))) =
        Algebra.TensorProduct.lift (SymmetricAlgebra.lift v) (SymmetricAlgebra.lift l)
          fun _ _ => Commute.all _ _ := by
      refine tensor_ext ?_ ?_
      · rw [AlgHom.comp_assoc, Algebra.TensorProduct.map_comp_includeLeft, ← AlgHom.comp_assoc,
          Algebra.TensorProduct.lift_comp_includeLeft,
          Algebra.TensorProduct.lift_comp_includeRight',
          Algebra.TensorProduct.lift_comp_includeLeft]
      · rw [AlgHom.comp_assoc, Algebra.TensorProduct.map_comp_includeRight, ← AlgHom.comp_assoc,
          Algebra.TensorProduct.lift_comp_includeRight', AlgHom.comp_id,
          Algebra.TensorProduct.lift_comp_includeRight']
    rw [key, lift_comp_symComul]

/-- The free action, computed on an arbitrary `B`-point of the product. -/
theorem translate_freeCoaction_point (Φ : (S ⊗[R] SymmetricAlgebra R F) →ₐ[R] B)
    (l : F →ₗ[R] B) :
    translate (freeCoaction R S F) Φ l =
      Algebra.TensorProduct.lift (Φ.comp Algebra.TensorProduct.includeLeft)
        (SymmetricAlgebra.lift
          (SymmetricAlgebra.lift.symm (Φ.comp Algebra.TensorProduct.includeRight) + l))
        (fun _ _ => Commute.all _ _) := by
  conv_lhs => rw [tensorPoint_eq Φ]
  rw [translate_freeCoaction]

/-- The free action of the vector bundle `E = Spec Sym(F)` on the product `C ×_{Spec R} E`. -/
noncomputable def freeAction {ψ : S →ₐ[R] Polynomial S} (h : IsConeCoaction ψ) :
    ConeAction R (S ⊗[R] SymmetricAlgebra R F) F where
  coaction := tensorCoaction ψ (symCoaction R F)
  isCone := isConeCoaction_tensorCoaction h (isConeCoaction_symCoaction R F)
  act := freeCoaction R S F
  act_zero := by
    intro B _ _ Φ
    conv_lhs => rw [tensorPoint_eq Φ]
    rw [translate_freeCoaction, add_zero, ← tensorPoint_eq]
  act_add := by
    intro B _ _ Φ l l'
    conv_lhs => rw [tensorPoint_eq Φ]
    conv_rhs => rw [tensorPoint_eq Φ]
    rw [translate_freeCoaction, translate_freeCoaction, translate_freeCoaction, add_assoc]
  conic := by
    refine isConeHom_tensor_ext ?_ ?_
    · rw [freeCoaction_comp_includeLeft]
      exact (isConeHom_includeLeft ψ (symCoaction R F)).comp
        (isConeHom_includeLeft (tensorCoaction ψ (symCoaction R F)) (symCoaction R F))
    · rw [freeCoaction_comp_includeRight]
      refine (translationAction R F).conic.comp (isConeHom_tensor_ext ?_ ?_)
      · rw [Algebra.TensorProduct.map_comp_includeLeft]
        exact (isConeHom_includeRight ψ (symCoaction R F)).comp
          (isConeHom_includeLeft (tensorCoaction ψ (symCoaction R F)) (symCoaction R F))
      · rw [Algebra.TensorProduct.map_comp_includeRight, AlgHom.comp_id]
        exact isConeHom_includeRight (tensorCoaction ψ (symCoaction R F)) (symCoaction R F)

variable {ψ : S →ₐ[R] Polynomial S} {h : IsConeCoaction ψ}

/-- The free action does not change the `C`-component of a point of `C ×_{Spec R} E`. -/
theorem freeCoaction_comp_translate (Φ : (S ⊗[R] SymmetricAlgebra R F) →ₐ[R] B)
    (l : F →ₗ[R] B) :
    (translate (freeCoaction R S F) Φ l).comp Algebra.TensorProduct.includeLeft =
      Φ.comp Algebra.TensorProduct.includeLeft := by
  rw [translate, AlgHom.comp_assoc, freeCoaction_comp_includeLeft, ← AlgHom.comp_assoc,
    Algebra.TensorProduct.lift_comp_includeLeft]

/-- The free action is free: a point of `C ×_{Spec R} E` has trivial stabiliser, and more
generally a translation between two points is unique. -/
theorem freeCoaction_translate_injective (Φ : (S ⊗[R] SymmetricAlgebra R F) →ₐ[R] B)
    {l₁ l₂ : F →ₗ[R] B}
    (heq : translate (freeCoaction R S F) Φ l₁ = translate (freeCoaction R S F) Φ l₂) :
    l₁ = l₂ := by
  rw [translate_freeCoaction_point, translate_freeCoaction_point] at heq
  have h1 := congrArg
    (fun k => SymmetricAlgebra.lift.symm
      (k.comp (Algebra.TensorProduct.includeRight :
        SymmetricAlgebra R F →ₐ[R] S ⊗[R] SymmetricAlgebra R F))) heq
  simp only [Algebra.TensorProduct.lift_comp_includeRight',
    SymmetricAlgebra.lift.symm_apply_apply] at h1
  exact add_left_cancel h1

/-- In the quotient of `C ×_{Spec R} E` by the free action there is at most one arrow between
any two objects. -/
instance freeAction_hom_subsingleton (Φ Ψ : QuotientGroupoid (freeAction (F := F) h) B) :
    Subsingleton (Φ ⟶ Ψ) where
  allEq f g := QuotientGroupoid.Hom.ext
    (freeCoaction_translate_injective Φ.point
      (f.translate_eq.trans g.translate_eq.symm))

/-- Two points of `C ×_{Spec R} E` become isomorphic in the quotient by the free action exactly
when their `C`-components agree: the quotient is `C`. -/
theorem freeAction_nonempty_hom_iff (Φ Ψ : QuotientGroupoid (freeAction (F := F) h) B) :
    Nonempty (Φ ⟶ Ψ) ↔
      Φ.point.comp Algebra.TensorProduct.includeLeft =
        Ψ.point.comp Algebra.TensorProduct.includeLeft := by
  constructor
  · rintro ⟨f⟩
    rw [← f.translate_eq]
    exact (freeCoaction_comp_translate Φ.point f.val).symm
  · intro hC
    refine ⟨⟨SymmetricAlgebra.lift.symm (Ψ.point.comp Algebra.TensorProduct.includeRight) -
      SymmetricAlgebra.lift.symm (Φ.point.comp Algebra.TensorProduct.includeRight), ?_⟩⟩
    change translate (freeCoaction R S F) Φ.point _ = Ψ.point
    rw [translate_freeCoaction_point, add_sub_cancel, hC, ← tensorPoint_eq]

/-- The canonical arrow from a point of `C ×_{Spec R} E` to the point with zero bundle
component. -/
theorem translate_neg_freeCoaction (Φ : (S ⊗[R] SymmetricAlgebra R F) →ₐ[R] B) :
    translate (freeCoaction R S F) Φ
        (-SymmetricAlgebra.lift.symm (Φ.comp Algebra.TensorProduct.includeRight)) =
      Algebra.TensorProduct.lift (Φ.comp Algebra.TensorProduct.includeLeft)
        (SymmetricAlgebra.lift (0 : F →ₗ[R] B)) (fun _ _ => Commute.all _ _) := by
  rw [translate_freeCoaction_point, add_neg_cancel]

/-- A free quotient is the honest quotient: the quotient groupoid of `C ×_{Spec R} E` by the
free action of `E` is equivalent to the discrete groupoid of `B`-points of `C`.  In particular
the constructed quotient really is the quotient of the torsor `C × E → C`. -/
noncomputable def freeQuotientEquivalence (B : Type u) [CommRing B] [Algebra R B] :
    QuotientGroupoid (freeAction (F := F) h) B ≌ Discrete (S →ₐ[R] B) where
  functor :=
    { obj := fun Φ => ⟨Φ.point.comp Algebra.TensorProduct.includeLeft⟩
      map := fun {Φ _} f => Discrete.eqToHom
        ((freeCoaction_comp_translate Φ.point f.val).symm.trans
          (congrArg (fun z => z.comp Algebra.TensorProduct.includeLeft) f.translate_eq))
      map_id := fun _ => Subsingleton.elim _ _
      map_comp := fun _ _ => Subsingleton.elim _ _ }
  inverse := Discrete.functor fun x =>
    (⟨Algebra.TensorProduct.lift x (SymmetricAlgebra.lift (0 : F →ₗ[R] B))
        fun _ _ => Commute.all _ _⟩ : QuotientGroupoid (freeAction (F := F) h) B)
  unitIso := NatIso.ofComponents
    (fun Φ => (Groupoid.isoEquivHom _ _).symm
      ⟨-SymmetricAlgebra.lift.symm
          (Φ.point.comp Algebra.TensorProduct.includeRight),
        translate_neg_freeCoaction Φ.point⟩)
    (fun _ => Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents
    (fun x => Discrete.eqToIso (Algebra.TensorProduct.lift_comp_includeLeft x.as
      (SymmetricAlgebra.lift (0 : F →ₗ[R] B)) fun _ _ => Commute.all _ _))
    (fun _ => Subsingleton.elim _ _)
  functor_unitIso_comp _ := Subsingleton.elim _ _

end FreeAction

/-! ### Exact sequences of cones -/

section Exact

variable {R S SD F : Type u} [CommRing R] [CommRing S] [Algebra R S] [CommRing SD]
  [Algebra R SD] [AddCommGroup F] [Module R F]

/-- Exactness of a sequence of cones `E → C → D` over `Spec R`, where the vector bundle
`E = Spec Sym(F)` acts on the cone `C = Spec S` and `φ : SD →ₐ[R] S` is the coordinate algebra
map of a morphism of cones `C → D = Spec SD`.  The conditions say that `C → D` is invariant,
surjective on points, that its fibres are exactly the orbits of `E`, and that the action is
free; equivalently, `D` is the quotient `[C/E]` and the quotient groupoid has trivial
stabilisers. -/
structure IsExactSequence (A : ConeAction R S F) (ψD : SD →ₐ[R] Polynomial SD)
    (φ : SD →ₐ[R] S) : Prop where
  /-- The map `C → D` is a morphism of cones. -/
  coneHom : IsConeHom ψD A.coaction φ
  /-- The map `C → D` is invariant under the action of `E`. -/
  invariant : ∀ {B : Type u} [CommRing B] [Algebra R B] (x : S →ₐ[R] B) (l : F →ₗ[R] B),
    (translate A.act x l).comp φ = x.comp φ
  /-- Every point of `D` lifts to a point of `C`. -/
  surjective : ∀ {B : Type u} [CommRing B] [Algebra R B] (y : SD →ₐ[R] B),
    ∃ x : S →ₐ[R] B, x.comp φ = y
  /-- Two points of `C` with the same image in `D` lie in the same orbit. -/
  orbit : ∀ {B : Type u} [CommRing B] [Algebra R B] (x y : S →ₐ[R] B),
    x.comp φ = y.comp φ → ∃ l : F →ₗ[R] B, translate A.act x l = y
  /-- The action is free. -/
  free : ∀ {B : Type u} [CommRing B] [Algebra R B] (x : S →ₐ[R] B) (l : F →ₗ[R] B),
    translate A.act x l = x → l = 0

namespace IsExactSequence

variable {A : ConeAction R S F} {ψD : SD →ₐ[R] Polynomial SD} {φ : SD →ₐ[R] S}
variable {B : Type u} [CommRing B] [Algebra R B]

/-- In an exact sequence the quotient groupoid has at most one arrow between two objects. -/
theorem hom_ext (h : IsExactSequence A ψD φ) {x y : QuotientGroupoid A B} (f g : x ⟶ y) :
    f = g := by
  refine QuotientGroupoid.Hom.ext (sub_eq_zero.1 (h.free x.point (f.val - g.val) ?_))
  have h1 : translate A.act (translate A.act x.point f.val) (-g.val) =
      translate A.act x.point (f.val - g.val) := by
    rw [A.act_add]
    congr 1
    abel
  rw [← h1, f.translate_eq, ← g.translate_eq, A.act_add, add_neg_cancel, A.act_zero]

/-- In an exact sequence, two points of `C` are isomorphic in the quotient exactly when they
have the same image in `D`. -/
theorem nonempty_hom_iff (h : IsExactSequence A ψD φ) (x y : QuotientGroupoid A B) :
    Nonempty (x ⟶ y) ↔ x.point.comp φ = y.point.comp φ := by
  refine ⟨fun ⟨f⟩ => ?_, fun hxy => ?_⟩
  · rw [← f.translate_eq, h.invariant]
  · obtain ⟨l, hl⟩ := h.orbit x.point y.point hxy
    exact ⟨⟨l, hl⟩⟩

/-- An exact sequence identifies the quotient groupoid `[C/E](B)` with the discrete groupoid of
`B`-points of `D`: the constructed quotient really is the cone `D`. -/
noncomputable def quotientEquivalence (h : IsExactSequence A ψD φ) (B : Type u) [CommRing B]
    [Algebra R B] : QuotientGroupoid A B ≌ Discrete (SD →ₐ[R] B) where
  functor :=
    { obj := fun x => ⟨x.point.comp φ⟩
      map := fun {x _} f => Discrete.eqToHom
        ((h.invariant x.point f.val).symm.trans
          (congrArg (fun z => z.comp φ) f.translate_eq))
      map_id := fun _ => Subsingleton.elim _ _
      map_comp := fun _ _ => Subsingleton.elim _ _ }
  inverse := Discrete.functor fun y =>
    (⟨(h.surjective y).choose⟩ : QuotientGroupoid A B)
  unitIso := NatIso.ofComponents
    (fun x => (Groupoid.isoEquivHom _ _).symm
      ⟨(h.orbit x.point (h.surjective (x.point.comp φ)).choose
          (h.surjective (x.point.comp φ)).choose_spec.symm).choose,
        (h.orbit x.point (h.surjective (x.point.comp φ)).choose
          (h.surjective (x.point.comp φ)).choose_spec.symm).choose_spec⟩)
    (fun _ => h.hom_ext _ _)
  counitIso := NatIso.ofComponents
    (fun y => Discrete.eqToIso (h.surjective y.as).choose_spec)
    (fun _ => Subsingleton.elim _ _)
  functor_unitIso_comp _ := Subsingleton.elim _ _

end IsExactSequence

/-- The free action of a vector bundle on a product sits in an exact sequence
`E → C ×_{Spec R} E → C`. -/
theorem isExactSequence_freeAction {ψ : S →ₐ[R] Polynomial S} (h : IsConeCoaction ψ) :
    IsExactSequence (freeAction (F := F) h) ψ
      (Algebra.TensorProduct.includeLeft : S →ₐ[R] S ⊗[R] SymmetricAlgebra R F) where
  coneHom := isConeHom_includeLeft ψ (symCoaction R F)
  invariant := by
    intro B _ _ x l
    exact freeCoaction_comp_translate x l
  surjective := by
    intro B _ _ y
    exact ⟨Algebra.TensorProduct.lift y (SymmetricAlgebra.lift (0 : F →ₗ[R] B))
      fun _ _ => Commute.all _ _, Algebra.TensorProduct.lift_comp_includeLeft _ _ _⟩
  orbit := by
    intro B _ _ x y hxy
    refine ⟨SymmetricAlgebra.lift.symm (y.comp Algebra.TensorProduct.includeRight) -
      SymmetricAlgebra.lift.symm (x.comp Algebra.TensorProduct.includeRight), ?_⟩
    change translate (freeCoaction R S F) x _ = y
    rw [translate_freeCoaction_point, add_sub_cancel, hxy, ← tensorPoint_eq]
  free := by
    intro B _ _ x l hl
    refine freeCoaction_translate_injective x (hl.trans ?_)
    exact ((freeAction (F := F) h).act_zero x).symm

end Exact

/-! ### The action as a morphism of schemes -/

section SchemeLevel

open _root_.AlgebraicGeometry

variable {R S F : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup F] [Module R F]

/-- The zero section `C → C ×_{Spec R} E` of a product with a vector bundle, on coordinate
algebras. -/
noncomputable def zeroSectionHom (R S F : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup F] [Module R F] : (S ⊗[R] SymmetricAlgebra R F) →ₐ[R] S :=
  Algebra.TensorProduct.lift (AlgHom.id R S) (SymmetricAlgebra.lift (0 : F →ₗ[R] S))
    fun _ _ => Commute.all _ _

/-- The action morphism `C ×_{Spec R} E → C` of affine schemes. -/
noncomputable def actionMap (A : ConeAction R S F) :
    Spec (CommRingCat.of (S ⊗[R] SymmetricAlgebra R F)) ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom A.act.toRingHom)

/-- The zero section `C → C ×_{Spec R} E` of affine schemes. -/
noncomputable def zeroSectionMap (R S F : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup F] [Module R F] :
    Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (S ⊗[R] SymmetricAlgebra R F)) :=
  Spec.map (CommRingCat.ofHom (zeroSectionHom R S F).toRingHom)

/-- Unit law for the action of schemes: acting by the zero section does nothing. -/
theorem zeroSectionMap_comp_actionMap (A : ConeAction R S F) :
    zeroSectionMap R S F ≫ actionMap A = 𝟙 _ := by
  rw [zeroSectionMap, actionMap, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  exact CommRingCat.hom_ext
    (congrArg AlgHom.toRingHom (A.act_zero (AlgHom.id R S)))

/-- The action morphism commutes with the contractions: the action of `E` on `C` is
`𝔾ₘ`-equivariant, as morphisms of schemes. -/
theorem actionMap_comp_contractionMap (A : ConeAction R S F) (r : R) :
    actionMap A ≫ contractionMap A.coaction r =
      contractionMap (tensorCoaction A.coaction (symCoaction R F)) r ≫ actionMap A := by
  rw [actionMap, contractionMap, contractionMap, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom (A.conic.comp_contraction r))

end SchemeLevel

end ConeQuotient

end GromovWitten.AlgebraicGeometry
