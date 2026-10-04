/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GromovWitten Contributors
-/

import GromovWitten.AlgebraicGeometry.Stacks.TorsorRepresentable
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.TotallySplit
import Mathlib.Algebra.Group.MinimalAxioms

/-!
# The constant finite group as an affine group

For a finite group `Γ` we build the constant group scheme `Γ` over `Spec ℤ` as an affine group
`Spec R_Γ`, `R_Γ = ConstantRing Γ = (Γ → TorsorZu)`, together with its group object on the fppf
sheaf of points, and specialise the round-26 atlas results to it.

* `B`-points. A ring homomorphism `φ : R_Γ →+* B` is determined by the complete orthogonal
  family of idempotents `e_γ = φ (δ_γ)` (`ConstantPoints.idem`, `ConstantPoints.ofIdem`,
  `ConstantPoints.ext_idem`), and the group law is the convolution
  `(e ⋆ f)_γ = ∑_α e_α f_{α⁻¹ γ}`; the unit is `δ_{γ,1}` and the inverse is `γ ↦ e_{γ⁻¹}`.
* The group object. The presheaf of groups `T ↦ ConstantPoints Γ Γ(T, ⊤)` on schemes is
  represented by `Spec R_Γ` (through the `Γ`–`Spec` adjunction), which gives a group object in
  schemes (`GrpObj.ofRepresentableBy`); its image under the finite-product-preserving functor
  `fppfYoneda` is the group object `constantGrpObj Γ` on the fppf sheaf of points.
* Properties. `R_Γ` is étale and finite over `ℤ` (it is isomorphic to `Γ → ℤ`, a finite split
  algebra), and `Spec R_Γ → Spec TorsorZu` is surjective (evaluation at `1` is a retraction).

## Main results

* `ConstantPoints Γ B` (the ring homomorphisms `R_Γ →+* B`), its `Group` instance and the
  naturality `ConstantPoints.map : ConstantPoints Γ B →* ConstantPoints Γ B'`.
* `constantSchemeGrpObj Γ : GrpObj (Spec R_Γ)`, with `constantHomEquiv_lift_mul`,
  `constantHomEquiv_toUnit_one`, `constantHomEquiv_comp_inv` identifying its group law on
  `T`-points with that of `ConstantPoints Γ Γ(T, ⊤)`.
* `constantGrpObj Γ : GrpObj (fppfYoneda.obj (Spec R_Γ))`, `constantGroup Γ :
  AlgebraicSpaceGroup` (`= affineGroup R_Γ (constantGrpObj Γ)`), and
  `lift_fppfYoneda_map_constantGrpObj_mul` (the group law on scheme-valued points).
* Instances `Algebra.Etale ℤ R_Γ`, `Module.Finite ℤ R_Γ` (also for `Ring.toIntAlgebra`), and
  `Module.Finite TorsorZu R_Γ`; `etale_torsorZu_constantRing`.
* `surjective_constant`: `Spec R_Γ → Spec TorsorZu` is surjective (for `torsorZuAlgebra`).
* `classifyingAtlasChart_constant_isEtaleSurjective`: the atlas `pt → BΓ` is étale and
  surjective; `exists_torsorRepresentation_constantGroup`: every `Γ`-torsor over a scheme is
  represented by a scheme étale, finite and surjective over the base.

The representable diagonal of `BΓ` is not proved here.
-/

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

namespace GromovWitten.AlgebraicGeometry

universe u v

noncomputable section

attribute [local instance] Fintype.ofFinite

section ConstantPoints

variable (Γ : Type u) [Finite Γ] [DecidableEq Γ]

/-- The ring of `TorsorZu`-valued functions on `Γ`, the coordinate ring of the constant group. -/
abbrev ConstantRing : Type u := Γ → TorsorZu.{u}

/-- The points of the constant group with values in a commutative ring `B`: ring homomorphisms
`(Γ → TorsorZu) →+* B`. -/
def ConstantPoints (B : Type v) [CommRing B] : Type (max u v) := ConstantRing Γ →+* B

variable {Γ}

namespace ConstantPoints

variable {B : Type v} [CommRing B]

/-- The underlying ring homomorphism of a point. -/
def toRingHom (φ : ConstantPoints Γ B) : ConstantRing Γ →+* B := φ

/-- A ring homomorphism, viewed as a point. -/
def ofRingHom (φ : ConstantRing Γ →+* B) : ConstantPoints Γ B := φ

/-- The idempotent `φ (δ_γ)` attached to a point `φ`. -/
def idem (φ : ConstantPoints Γ B) (γ : Γ) : B := φ.toRingHom (Pi.single γ 1)

/-- The idempotents `φ (δ_γ)` of a point form a complete orthogonal family. -/
theorem completeOrthogonalIdempotents_idem (φ : ConstantPoints Γ B) :
    CompleteOrthogonalIdempotents φ.idem :=
  (CompleteOrthogonalIdempotents.single (fun _ : Γ => TorsorZu.{u})).map φ.toRingHom

/-- The ring homomorphism attached to a complete family of orthogonal idempotents. -/
def ofIdem (e : Γ → B) (he : CompleteOrthogonalIdempotents e) : ConstantPoints Γ B := ofRingHom
  {
  toFun g := ∑ γ, ((g γ).down : B) * e γ
  map_one' := by simpa using he.complete
  map_mul' g h := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [Finset.sum_eq_single γ]
    · rw [mul_mul_mul_comm, he.toOrthogonalIdempotents.mul_eq, if_pos rfl]
      change (((g γ).down * (h γ).down : ℤ) : B) * e γ = _
      push_cast; ring
    · intro δ _ hδ
      rw [mul_mul_mul_comm, he.toOrthogonalIdempotents.mul_eq, if_neg (Ne.symm hδ), mul_zero]
    · simp
  map_zero' := by simp
  map_add' g h := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun γ _ => ?_
    change (((g γ).down + (h γ).down : ℤ) : B) * e γ = _
    push_cast; ring }

/-- The idempotent family of `ofIdem e he` is `e`. -/
theorem idem_ofIdem (e : Γ → B) (he : CompleteOrthogonalIdempotents e) :
    (ofIdem e he).idem = e := by
  funext γ
  change ∑ δ, (((Pi.single γ (1 : TorsorZu.{u}) : Γ → TorsorZu.{u}) δ).down : B) * e δ = e γ
  rw [Finset.sum_eq_single γ]
  · simp
  · intro δ _ hδ; simp [hδ]
  · simp

/-- Every point is the ring homomorphism attached to its idempotent family. -/
theorem ofIdem_idem (χ : ConstantPoints Γ B) :
    ofIdem χ.idem (completeOrthogonalIdempotents_idem χ) = χ := by
  change ofRingHom _ = ofRingHom χ.toRingHom
  congr 1
  refine RingHom.ext fun g => ?_
  have hg : g = ∑ γ, (((g γ).down : ConstantRing Γ)) * Pi.single γ 1 := by
    funext δ
    rw [Finset.sum_apply, Finset.sum_eq_single δ]
    · ext; simp
    · intro γ _ hγ; simp [Ne.symm hγ]
    · simp
  change ∑ γ, ((g γ).down : B) * χ.idem γ = χ.toRingHom g
  conv_rhs => rw [hg]
  rw [map_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [map_mul, map_intCast]
  rfl

/-- Points are determined by their idempotent families. -/
theorem ext_idem {φ ψ : ConstantPoints Γ B} (h : φ.idem = ψ.idem) : φ = ψ := by
  rw [← ofIdem_idem φ, ← ofIdem_idem ψ]
  congr 1

/-! ### The group law: convolution of idempotent families -/

variable [Group Γ]

/-- Convolution of two `Γ`-indexed families: `(e ⋆ f)_γ = ∑_α e_α f_{α⁻¹ γ}`. -/
def conv (e f : Γ → B) (γ : Γ) : B := ∑ α, e α * f (α⁻¹ * γ)

omit [DecidableEq Γ] in
/-- Convolution of `Γ`-indexed families is associative. -/
theorem conv_assoc (e f g : Γ → B) : conv (conv e f) g = conv e (conv f g) := by
  funext γ
  simp only [conv, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => ?_
  refine (Fintype.sum_equiv (Equiv.mulLeft β) _ _ fun α => ?_).symm
  simp [mul_assoc]

omit [DecidableEq Γ] in
/-- The convolution of two complete orthogonal idempotent families is again one. -/
theorem conv_completeOrthogonalIdempotents {e f : Γ → B} (he : CompleteOrthogonalIdempotents e)
    (hf : CompleteOrthogonalIdempotents f) : CompleteOrthogonalIdempotents (conv e f) := by
  classical
  refine ⟨OrthogonalIdempotents.iff_mul_eq.2 fun γ γ' => ?_, ?_⟩
  · have key : ∀ α α', e α * f (α⁻¹ * γ) * (e α' * f (α'⁻¹ * γ')) =
        if α' = α then e α * (f (α⁻¹ * γ) * f (α⁻¹ * γ')) else 0 := by
      intro α α'
      rw [mul_mul_mul_comm, he.toOrthogonalIdempotents.mul_eq]
      split_ifs with h1 h2 h2
      · subst h1; ring
      · exact absurd h1.symm h2
      · exact absurd h2.symm h1
      · simp
    simp only [conv, Finset.sum_mul_sum, key, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      hf.toOrthogonalIdempotents.mul_eq, mul_right_inj, mul_ite,
      mul_zero]
    split_ifs <;> simp
  · simp only [conv]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have hsum : ∀ y : Γ, ∑ x, f (y⁻¹ * x) = 1 := fun y =>
      (Fintype.sum_equiv (Equiv.mulLeft y⁻¹) _ _ fun _ => rfl).trans hf.complete
    simp [hsum, he.complete]

/-- The family `δ_{γ, 1}` is a complete orthogonal family of idempotents. -/
theorem completeOrthogonalIdempotents_unit :
    CompleteOrthogonalIdempotents (Pi.single (M := fun _ : Γ => B) 1 1) := by
  refine ⟨OrthogonalIdempotents.iff_mul_eq.2 fun γ γ' => ?_, ?_⟩
  · by_cases h : γ = γ'
    · subst h; by_cases h1 : γ = 1 <;> simp [h1]
    · rw [if_neg h]
      by_cases h1 : γ = 1
      · subst h1; simp [Ne.symm h]
      · simp [Pi.single_apply, h1]
  · simp

/-- The group law on `B`-points of the constant group: convolution of idempotent families. -/
instance : Mul (ConstantPoints Γ B) :=
  ⟨fun φ ψ => ofIdem (conv φ.idem ψ.idem) (conv_completeOrthogonalIdempotents
    (completeOrthogonalIdempotents_idem φ) (completeOrthogonalIdempotents_idem ψ))⟩

/-- The unit `B`-point: the idempotent family `δ_{γ, 1}` (evaluation at `1 : Γ`). -/
instance : One (ConstantPoints Γ B) :=
  ⟨ofIdem (Pi.single 1 1) completeOrthogonalIdempotents_unit⟩

/-- The inverse of a `B`-point: the idempotent family `γ ↦ e_{γ⁻¹}`. -/
instance : Inv (ConstantPoints Γ B) :=
  ⟨fun φ => ofIdem (fun γ => φ.idem γ⁻¹)
    ((CompleteOrthogonalIdempotents.equiv (Equiv.inv Γ)).2
      (completeOrthogonalIdempotents_idem φ))⟩

/-- The idempotent family of a product is the convolution of the families. -/
theorem idem_mul (φ ψ : ConstantPoints Γ B) : (φ * ψ).idem = conv φ.idem ψ.idem :=
  idem_ofIdem _ _

/-- The idempotent family of the unit is `δ_{γ, 1}`. -/
theorem idem_one : (1 : ConstantPoints Γ B).idem = Pi.single 1 1 :=
  idem_ofIdem _ _

/-- The idempotent family of the inverse is `γ ↦ e_{γ⁻¹}`. -/
theorem idem_inv (φ : ConstantPoints Γ B) : φ⁻¹.idem = fun γ => φ.idem γ⁻¹ :=
  idem_ofIdem _ _

/-- The `B`-points of the constant group `Γ` form a group under the convolution product of
idempotent families. -/
instance : Group (ConstantPoints Γ B) := Group.ofLeftAxioms
  (fun φ ψ χ => ext_idem (by simp only [idem_mul, conv_assoc]))
  (fun φ => ext_idem (by
    rw [idem_mul, idem_one]
    funext γ
    simp [conv, Pi.single_apply]))
  (fun φ => ext_idem (by
    rw [idem_mul, idem_inv, idem_one]
    funext γ
    have he := (completeOrthogonalIdempotents_idem φ).toOrthogonalIdempotents
    simp only [conv, he.mul_eq]
    by_cases hγ : γ = 1
    · subst hγ
      simpa using (Fintype.sum_equiv (Equiv.inv Γ) _ _ fun _ => rfl).trans
        (completeOrthogonalIdempotents_idem φ).complete
    · rw [Pi.single_eq_of_ne hγ]
      refine Finset.sum_eq_zero fun α _ => ?_
      rw [if_neg]
      intro h
      exact hγ (by simpa using h)))

variable {B' : Type*} [CommRing B']

omit [Group Γ] [Finite Γ] in
/-- The idempotent family of `h ∘ φ` is `h ∘ (idempotent family of φ)`. -/
theorem idem_ofRingHom_comp (h : B →+* B') (φ : ConstantPoints Γ B) :
    (ofRingHom (h.comp φ.toRingHom)).idem = h ∘ φ.idem := rfl

/-- Naturality: a ring homomorphism `h : B →+* B'` induces a group homomorphism on points,
`φ ↦ h ∘ φ`. -/
def map (h : B →+* B') : ConstantPoints Γ B →* ConstantPoints Γ B' where
  toFun φ := ofRingHom (h.comp φ.toRingHom)
  map_one' := ext_idem (by
    rw [idem_ofRingHom_comp, idem_one, idem_one]
    funext γ
    by_cases hγ : γ = 1
    · subst hγ; simp
    · simp [Pi.single_eq_of_ne hγ])
  map_mul' φ ψ := ext_idem (by
    rw [idem_ofRingHom_comp, idem_mul, idem_mul, idem_ofRingHom_comp, idem_ofRingHom_comp]
    funext γ
    simp only [Function.comp_apply, conv, map_sum, map_mul])

/-- The idempotent family of `map h φ` is `h ∘ φ.idem`. -/
theorem idem_map (h : B →+* B') (φ : ConstantPoints Γ B) : (map h φ).idem = h ∘ φ.idem := rfl

/-- The ring homomorphism underlying `map h φ` is `h.comp φ`. -/
theorem toRingHom_map (h : B →+* B') (φ : ConstantPoints Γ B) :
    (map h φ).toRingHom = h.comp φ.toRingHom := rfl

end ConstantPoints

end ConstantPoints

/-! ### The group object on `Spec (Γ → TorsorZu)` -/

section GroupObject

variable (Γ : Type u) [Group Γ] [Finite Γ] [DecidableEq Γ]

/-- The presheaf of groups `T ↦ ConstantPoints Γ Γ(T, ⊤)` on schemes. -/
@[simps]
noncomputable def constantPointsFunctor : Scheme.{u}ᵒᵖ ⥤ GrpCat.{u} where
  obj T := GrpCat.of (ConstantPoints Γ Γ(T.unop, ⊤))
  map f := GrpCat.ofHom (ConstantPoints.map f.unop.appTop.hom)
  map_id T := GrpCat.hom_ext (MonoidHom.ext fun φ => ConstantPoints.ext_idem (by
    change (ConstantPoints.map _ φ).idem = φ.idem
    rw [ConstantPoints.idem_map]
    simp))
  map_comp f g := GrpCat.hom_ext (MonoidHom.ext fun φ => ConstantPoints.ext_idem (by
    change (ConstantPoints.map _ φ).idem =
      (ConstantPoints.map _ (ConstantPoints.map _ φ)).idem
    rw [ConstantPoints.idem_map, ConstantPoints.idem_map, ConstantPoints.idem_map]
    rfl))

/-- The natural bijection `(T ⟶ Spec (Γ → TorsorZu)) ≃ ConstantPoints Γ Γ(T, ⊤)`, sending `f` to
the ring homomorphism `Γ → TorsorZu ≅ Γ(Spec _, ⊤) ⟶ Γ(T, ⊤)` induced by `f`. -/
noncomputable def constantHomEquiv (T : Scheme.{u}) :
    (T ⟶ Spec (CommRingCat.of (ConstantRing Γ))) ≃ ConstantPoints Γ Γ(T, ⊤) where
  toFun f := ConstantPoints.ofRingHom ((Scheme.ΓSpecIso (CommRingCat.of _)).inv ≫ f.appTop).hom
  invFun φ := ΓSpec.adjunction.homEquiv T (Opposite.op (CommRingCat.of (ConstantRing Γ)))
    (CommRingCat.ofHom φ.toRingHom).op
  left_inv f := by
    apply ext_to_Spec
    rw [Scheme.Γ_map_op, Scheme.Γ_map_op]
    exact ΓSpecIso_inv_ΓSpec_adjunction_homEquiv (X := T)
      (CommRingCat.ofHom ((Scheme.ΓSpecIso (CommRingCat.of _)).inv ≫ f.appTop).hom)
  right_inv φ := by
    have h := ΓSpecIso_inv_ΓSpec_adjunction_homEquiv (X := T)
      (CommRingCat.ofHom (ConstantPoints.toRingHom φ))
    exact congrArg (fun k => ConstantPoints.ofRingHom k.hom) h

omit [Group Γ] [Finite Γ] [DecidableEq Γ] in
/-- The ring homomorphism attached to `f : T ⟶ Spec (Γ → TorsorZu)`. -/
theorem constantHomEquiv_toRingHom {T : Scheme.{u}}
    (f : T ⟶ Spec (CommRingCat.of (ConstantRing Γ))) :
    (constantHomEquiv Γ T f).toRingHom =
      ((Scheme.ΓSpecIso (CommRingCat.of _)).inv ≫ f.appTop).hom := rfl

/-- Naturality of `constantHomEquiv` in `T`. -/
theorem constantHomEquiv_comp {T T' : Scheme.{u}} (g : T' ⟶ T)
    (f : T ⟶ Spec (CommRingCat.of (ConstantRing Γ))) :
    constantHomEquiv Γ T' (g ≫ f) = ConstantPoints.map g.appTop.hom (constantHomEquiv Γ T f) := by
  change ConstantPoints.ofRingHom
      ((Scheme.ΓSpecIso (CommRingCat.of _)).inv ≫ (g ≫ f).appTop).hom =
    ConstantPoints.ofRingHom
      (g.appTop.hom.comp ((Scheme.ΓSpecIso (CommRingCat.of _)).inv ≫ f.appTop).hom)
  rw [Scheme.Hom.comp_appTop]
  rfl

/-- `Spec (Γ → TorsorZu)` represents the presheaf of sets underlying `constantPointsFunctor Γ`. -/
noncomputable def constantRepresentableBy :
    (constantPointsFunctor Γ ⋙ forget GrpCat).RepresentableBy
      (Spec (CommRingCat.of (ConstantRing Γ))) where
  homEquiv {T} := constantHomEquiv Γ T
  homEquiv_comp g f := constantHomEquiv_comp Γ g f

/-- The group-scheme structure on `Spec (Γ → TorsorZu)`: the constant group scheme `Γ` over
`Spec ℤ`, as a group object in the category of schemes. -/
@[instance_reducible]
noncomputable def constantSchemeGrpObj : GrpObj (Spec (CommRingCat.of (ConstantRing Γ))) :=
  GrpObj.ofRepresentableBy _ (constantPointsFunctor Γ) (constantRepresentableBy Γ)

/-- The group law of `constantSchemeGrpObj Γ` on `T`-points is the convolution product of
`ConstantPoints`: `constantHomEquiv (lift a b ≫ μ) = constantHomEquiv a * constantHomEquiv b`. -/
theorem constantHomEquiv_lift_mul {T : Scheme.{u}}
    (a b : T ⟶ Spec (CommRingCat.of (ConstantRing Γ))) :
    constantHomEquiv Γ T (lift a b ≫ (constantSchemeGrpObj Γ).mul) =
      constantHomEquiv Γ T a * constantHomEquiv Γ T b := by
  let α := constantRepresentableBy Γ
  have hμ : (constantSchemeGrpObj Γ).mul =
      α.homEquiv'.symm (α.homEquiv' (fst _ _) * α.homEquiv' (snd _ _)) := rfl
  change α.homEquiv' (lift a b ≫ _) = α.homEquiv' a * α.homEquiv' b
  rw [hμ, α.homEquiv'_comp, Equiv.apply_symm_apply, map_mul, ← α.homEquiv'_comp,
    ← α.homEquiv'_comp, lift_fst, lift_snd]

/-- The unit of `constantSchemeGrpObj Γ` on `T`-points is the unit of `ConstantPoints`. -/
theorem constantHomEquiv_toUnit_one (T : Scheme.{u}) :
    constantHomEquiv Γ T (toUnit T ≫ (constantSchemeGrpObj Γ).one) = 1 := by
  let α := constantRepresentableBy Γ
  have hη : (constantSchemeGrpObj Γ).one = α.homEquiv'.symm 1 := rfl
  change α.homEquiv' (toUnit T ≫ _) = 1
  rw [hη, α.homEquiv'_comp, Equiv.apply_symm_apply, map_one]

/-- The inverse of `constantSchemeGrpObj Γ` on `T`-points is the inverse of `ConstantPoints`. -/
theorem constantHomEquiv_comp_inv {T : Scheme.{u}}
    (a : T ⟶ Spec (CommRingCat.of (ConstantRing Γ))) :
    constantHomEquiv Γ T (a ≫ (constantSchemeGrpObj Γ).inv) = (constantHomEquiv Γ T a)⁻¹ := by
  let α := constantRepresentableBy Γ
  have hι : (constantSchemeGrpObj Γ).inv = α.homEquiv'.symm (α.homEquiv' (𝟙 _))⁻¹ := rfl
  change α.homEquiv' (a ≫ _) = (α.homEquiv' a)⁻¹
  rw [hι, α.homEquiv'_comp, Equiv.apply_symm_apply, map_inv, ← α.homEquiv'_comp,
    Category.comp_id]

end GroupObject

/-! ### The constant group as an fppf group sheaf -/

section FppfGroup

variable (Γ : Type u) [Group Γ] [Finite Γ] [DecidableEq Γ]

/-- **The constant group object** on the fppf sheaf of points of `Spec (Γ → TorsorZu)`: the image
of the scheme group object `constantSchemeGrpObj Γ` under the finite-product-preserving functor
`fppfYoneda`. -/
@[instance_reducible]
noncomputable def constantGrpObj :
    GrpObj (fppfYoneda.obj (Spec (CommRingCat.of (ConstantRing Γ)))) :=
  letI := constantSchemeGrpObj Γ
  letI : fppfYoneda.Monoidal := Functor.Monoidal.ofChosenFiniteProducts fppfYoneda
  Functor.grpObjObj

/-- **The constant finite group `Γ`** as an affine group algebraic space:
`affineGroup (Γ → TorsorZu) (constantGrpObj Γ)`. -/
noncomputable def constantGroup : AlgebraicSpaceGroup.{u} :=
  affineGroup (ConstantRing Γ) (constantGrpObj Γ)

/-- The group structure of `constantGroup Γ` is `constantGrpObj Γ` (by definition). -/
theorem constantGroup_group : (constantGroup Γ).group = constantGrpObj Γ := rfl

/-- **The group law of `constantGroup Γ` on scheme-valued points**: for `a b : T ⟶ Spec R_Γ`,
the product of the sheaf maps `fppfYoneda.map a`, `fppfYoneda.map b` under the group law of
`constantGrpObj Γ` is `fppfYoneda.map` of the morphism whose `ConstantPoints` is the
convolution product `constantHomEquiv a * constantHomEquiv b`. -/
theorem lift_fppfYoneda_map_constantGrpObj_mul {T : Scheme.{u}}
    (a b : T ⟶ Spec (CommRingCat.of (ConstantRing Γ))) :
    lift (fppfYoneda.map a) (fppfYoneda.map b) ≫ (constantGrpObj Γ).mul =
      fppfYoneda.map ((constantHomEquiv Γ T).symm
        (constantHomEquiv Γ T a * constantHomEquiv Γ T b)) := by
  let _ : fppfYoneda.{u}.Monoidal := Functor.Monoidal.ofChosenFiniteProducts fppfYoneda.{u}
  have hμ : (constantGrpObj Γ).mul = Functor.LaxMonoidal.μ fppfYoneda.{u} _ _ ≫
      fppfYoneda.{u}.map (constantSchemeGrpObj Γ).mul := rfl
  rw [hμ, Functor.Monoidal.lift_μ_assoc, ← Functor.map_comp, ← constantHomEquiv_lift_mul,
    Equiv.symm_apply_apply]

end FppfGroup


/-! ### Étaleness, finiteness, surjectivity; the atlas of `BΓ` -/

section Properties

variable (Γ : Type u) [Group Γ] [Finite Γ] [DecidableEq Γ]

/-- The ring isomorphism `(Γ → TorsorZu) ≃+* (Γ → ℤ)`, componentwise `ULift.ringEquiv`. -/
noncomputable def constantRingEquivInt : ConstantRing Γ ≃+* (Γ → ℤ) :=
  RingEquiv.piCongrRight fun _ => ULift.ringEquiv

/-- The `ℤ`-algebra isomorphism `(Γ → ℤ) ≃ₐ[ℤ] (Γ → TorsorZu)` (inverse of
`constantRingEquivInt`). -/
noncomputable def constantAlgEquivInt : (Γ → ℤ) ≃ₐ[ℤ] ConstantRing Γ :=
  AlgEquiv.ofRingEquiv (f := (constantRingEquivInt Γ).symm) fun n =>
    RingHom.congr_fun (RingHom.ext_int
      ((constantRingEquivInt Γ).symm.toRingHom.comp (algebraMap ℤ (Γ → ℤ)))
      (algebraMap ℤ (ConstantRing Γ))) n

/-- `Γ → TorsorZu` is an étale `ℤ`-algebra (it is isomorphic to the split algebra `Γ → ℤ`). -/
instance : Algebra.Etale ℤ (ConstantRing Γ) :=
  Algebra.Etale.of_equiv (constantAlgEquivInt Γ)

/-- `Γ → TorsorZu` is a finite `ℤ`-module. -/
instance : Module.Finite ℤ (ConstantRing Γ) :=
  Module.Finite.equiv (constantAlgEquivInt Γ).toLinearEquiv

/-- `Γ → TorsorZu` is étale over `ℤ` for the canonical `ℤ`-algebra structure
`Ring.toIntAlgebra` (the form used by the `_of_int` results of `TorsorRepresentable.lean`). -/
instance etale_int_constantRing :
    @Algebra.Etale ℤ (ConstantRing Γ) _ _ (Ring.toIntAlgebra (ConstantRing Γ)) := by
  have h : Ring.toIntAlgebra (ConstantRing Γ) = Pi.algebra _ _ := Subsingleton.elim _ _
  rw [h]
  exact Algebra.Etale.of_equiv (constantAlgEquivInt Γ)


omit [Group Γ] [DecidableEq Γ] in
/-- `Γ → TorsorZu` is étale over `TorsorZu`, for the algebra structure `torsorZuAlgebra`. -/
theorem etale_torsorZu_constantRing :
    @Algebra.Etale TorsorZu.{u} (ConstantRing Γ) _ _ (torsorZuAlgebra (ConstantRing Γ)) :=
  etale_torsorZu_of_etale

omit [Group Γ] [DecidableEq Γ] in
/-- `Γ → TorsorZu` is a finite `TorsorZu`-module (for the instance `ULift.module`). -/
instance finite_torsorZu_constantRing : Module.Finite TorsorZu.{u} (ConstantRing Γ) :=
  finite_torsorZu_of_finite

omit [Finite Γ] [DecidableEq Γ] in
/-- **`Spec (Γ → TorsorZu) → Spec TorsorZu` is surjective** (for the algebra structure
`torsorZuAlgebra`): evaluation at `1 : Γ` is a retraction of the structure map, so
`Spec.map` of it is a section. -/
theorem surjective_constant : _root_.AlgebraicGeometry.Surjective
    (@Spec.map (CommRingCat.of TorsorZu.{u}) (CommRingCat.of (ConstantRing Γ))
      (CommRingCat.ofHom (@algebraMap TorsorZu.{u} (ConstantRing Γ) _ _
        (torsorZuAlgebra (ConstantRing Γ))))) := by
  let alg : TorsorZu.{u} →+* ConstantRing Γ :=
    @algebraMap TorsorZu.{u} (ConstantRing Γ) _ _ (torsorZuAlgebra (ConstantRing Γ))
  let ev : ConstantRing Γ →+* TorsorZu.{u} := Pi.evalRingHom _ 1
  have hcomp : ev.comp alg = RingHom.id _ := by
    have e : TorsorZu.{u} ≃+* ℤ := ULift.ringEquiv
    have key : (ev.comp alg).comp e.symm.toRingHom = (RingHom.id _).comp e.symm.toRingHom :=
      RingHom.ext_int _ _
    ext z
    have hz : z = e.symm (e z) := (e.symm_apply_apply z).symm
    rw [hz]
    exact congrArg ULift.down (RingHom.congr_fun key (e z))
  have : _root_.AlgebraicGeometry.Surjective
      (Spec.map (CommRingCat.ofHom ev) ≫ Spec.map (CommRingCat.ofHom alg)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
    change _root_.AlgebraicGeometry.Surjective (Spec.map (𝟙 _))
    rw [Spec.map_id]
    infer_instance
  exact _root_.AlgebraicGeometry.Surjective.of_comp (Spec.map (CommRingCat.ofHom ev)) _

/-- **The atlas `pt → BΓ` is étale and surjective** for the constant finite group `Γ`. -/
theorem classifyingAtlasChart_constant_isEtaleSurjective :
    (ActionTorsor.classifyingAtlasChart (constantGroup Γ)).IsEtaleSurjective :=
  ActionTorsor.classifyingAtlasChart_affineGroup_isEtaleSurjective_of_int
    (surjective_constant Γ)

/-- **Torsors under the constant finite group are schemes**: every fppf `constantGroup Γ`-torsor
over a scheme `T` is represented by a scheme étale, finite and surjective over `T`. -/
theorem exists_torsorRepresentation_constantGroup {T : Scheme.{u}}
    (P : FppfTorsor (constantGroup Γ) T) :
    ∃ Rp : TorsorRepresentation P, _root_.AlgebraicGeometry.Etale Rp.toBase ∧
      IsFinite Rp.toBase ∧ _root_.AlgebraicGeometry.Surjective Rp.toBase :=
  FppfTorsor.exists_torsorRepresentation_affineGroup_of_int (surjective_constant Γ) P

end Properties

end

end GromovWitten.AlgebraicGeometry
