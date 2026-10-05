/-
Copyright (c) 2026 GromovWitten Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Additive functors and extension of complexes

An additive functor commutes with extension by zero along a complex-shape embedding.
The comparison is natural, identifies homology at embedded indices, and transfers a
quasi-isomorphism of mapped complexes to their extensions.
-/

open CategoryTheory Limits HomologicalComplex
namespace CategoryTheory.Functor

variable {A B : Type*} [Category* A] [Preadditive A] [HasZeroObject A]
  [Category* B] [Preadditive B] [HasZeroObject B]
  (H : A ⥤ B) [H.Additive]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (e : c.Embedding c') (K : HomologicalComplex A c)

/-- Applying an additive functor commutes with each term of extension by zero. -/
noncomputable def mapExtendXIso (j : ι') :
    H.obj ((K.extend e).X j) ≅ (((H.mapHomologicalComplex c).obj K).extend e).X j := by
  classical
  by_cases h : ∃ i, e.f i = j
  · exact H.mapIso (K.extendXIso e h.choose_spec) ≪≫
      (((H.mapHomologicalComplex c).obj K).extendXIso e h.choose_spec).symm
  · exact (H.map_isZero (K.isZero_extend_X e j (by simpa using h))).iso
      (((H.mapHomologicalComplex c).obj K).isZero_extend_X e j (by simpa using h))

set_option backward.isDefEq.respectTransparency false in
/-- The term comparison at an index in the image of the embedding. -/
lemma mapExtendXIso_at (i : ι) :
    mapExtendXIso H e K (e.f i) = H.mapIso (K.extendXIso e rfl) ≪≫
      (((H.mapHomologicalComplex c).obj K).extendXIso e rfl).symm := by
  classical
  have h : ∃ j, e.f j = e.f i := ⟨i, rfl⟩
  simp only [mapExtendXIso, dif_pos h]
  have aux (j : ι) (hj : e.f j = e.f i) :
      H.mapIso (K.extendXIso e hj) ≪≫
        (((H.mapHomologicalComplex c).obj K).extendXIso e hj).symm =
      H.mapIso (K.extendXIso e (i := i) rfl) ≪≫
        (((H.mapHomologicalComplex c).obj K).extendXIso e (i := i) rfl).symm := by
    have he : j = i := e.injective_f hj
    subst j
    rfl
  exact aux h.choose h.choose_spec

set_option backward.isDefEq.respectTransparency false in
/-- Applying an additive functor commutes with extension of a complex by zero. -/
noncomputable def mapExtendIso :
    (H.mapHomologicalComplex c').obj (K.extend e) ≅
      ((H.mapHomologicalComplex c).obj K).extend e := by
  classical
  refine HomologicalComplex.Hom.isoOfComponents (mapExtendXIso H e K) ?_
  intro i j hij
  by_cases hi : ∃ a, e.f a = i
  · obtain ⟨a, rfl⟩ := hi
    by_cases hj : ∃ b, e.f b = j
    · obtain ⟨b, rfl⟩ := hj
      rw [mapExtendXIso_at, mapExtendXIso_at]
      symm
      change H.map ((K.extend e).d (e.f a) (e.f b)) ≫
        (H.mapIso (K.extendXIso e rfl) ≪≫
          (((H.mapHomologicalComplex c).obj K).extendXIso e rfl).symm).hom = _
      simp only [K.extend_d_eq e rfl rfl,
        ((H.mapHomologicalComplex c).obj K).extend_d_eq e rfl rfl,
        Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, H.map_comp,
        Category.assoc, Iso.inv_hom_id_assoc, Functor.mapHomologicalComplex_obj_d]
      have hb : H.map (K.extendXIso e (i := b) rfl).inv ≫
          H.map (K.extendXIso e (i := b) rfl).hom = 𝟙 _ :=
        (H.mapIso (K.extendXIso e (i := b) rfl)).inv_hom_id
      simp only [reassoc_of% hb]
    · exact (((H.mapHomologicalComplex c).obj K).isZero_extend_X e j
        (by simpa using hj)).eq_of_tgt _ _
  · exact (H.map_isZero (K.isZero_extend_X e i (by simpa using hi))).eq_of_src _ _

/-- Extension by zero preserves the homology of the mapped complex at embedded indices. -/
noncomputable def mapExtendHomologyIso [CategoryWithHomology B]
    (i : ι) :
    ((H.mapHomologicalComplex c').obj (K.extend e)).homology (e.f i) ≅
      ((H.mapHomologicalComplex c).obj K).homology i :=
  (homologyFunctor B c' (e.f i)).mapIso (mapExtendIso H e K) ≪≫
    ((H.mapHomologicalComplex c).obj K).extendHomologyIso e rfl

set_option backward.isDefEq.respectTransparency false in
/-- The extension comparison commutes with maps of complexes. -/
lemma mapExtendIso_hom_naturality {L : HomologicalComplex A c} (f : K ⟶ L) :
    (H.mapHomologicalComplex c').map (extendMap f e) ≫ (mapExtendIso H e L).hom =
      (mapExtendIso H e K).hom ≫ extendMap ((H.mapHomologicalComplex c).map f) e := by
  apply HomologicalComplex.hom_ext
  intro j
  by_cases hj : ∃ i, e.f i = j
  · obtain ⟨i, rfl⟩ := hj
    change H.map ((extendMap f e).f (e.f i)) ≫ (mapExtendXIso H e L (e.f i)).hom =
      (mapExtendXIso H e K (e.f i)).hom ≫
        (extendMap ((H.mapHomologicalComplex c).map f) e).f (e.f i)
    rw [mapExtendXIso_at, mapExtendXIso_at, extendMap_f f e rfl,
      extendMap_f ((H.mapHomologicalComplex c).map f) e rfl]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, H.map_comp,
      Category.assoc, Iso.inv_hom_id_assoc, Functor.mapHomologicalComplex_map_f]
    have hi : H.map (L.extendXIso e (i := i) rfl).inv ≫
        H.map (L.extendXIso e (i := i) rfl).hom = 𝟙 _ :=
      (H.mapIso (L.extendXIso e (i := i) rfl)).inv_hom_id
    simp only [reassoc_of% hi]
  · exact (H.map_isZero (K.isZero_extend_X e j (by simpa using hj))).eq_of_src _ _

/-- A map that becomes a quasi-isomorphism after applying a functor retains this property
after extension by zero. -/
lemma quasiIso_map_extendMap [CategoryWithHomology B]
    {L : HomologicalComplex A c} (f : K ⟶ L)
    [QuasiIso ((H.mapHomologicalComplex c).map f)] :
    QuasiIso ((H.mapHomologicalComplex c').map (extendMap f e)) := by
  have : QuasiIso (extendMap ((H.mapHomologicalComplex c).map f) e) :=
    (quasiIso_extendMap_iff _ e).mpr inferInstance
  have hcomp : QuasiIso
      ((H.mapHomologicalComplex c').map (extendMap f e) ≫ (mapExtendIso H e L).hom) := by
    rw [mapExtendIso_hom_naturality]
    infer_instance
  exact (quasiIso_iff_comp_right _ (mapExtendIso H e L).hom).mp hcomp

end CategoryTheory.Functor
