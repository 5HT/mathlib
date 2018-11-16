import category_theory.adjunction
import category_theory.opposites
import category_theory.types
import category_theory.yoneda
import category_theory.limits
import category_theory.limits.functor_category
import category_theory.limits.types
import data.equiv.basic

namespace category_theory
open category_theory.limits

universes u v


-- TODO: Move this
section
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

def coext_equiv {X Y : C}
  (e : Π {Z : C}, (Y ⟶ Z) ≃ (X ⟶ Z))
  (n : Π {Z Z' : C} (f : Z ⟶ Z') (g : Y ⟶ Z), e.to_fun (g ≫ f) = e.to_fun g ≫ f) : X ≅ Y :=
{ hom := e.to_fun (𝟙 _),
  inv := e.inv_fun (𝟙 _),
  hom_inv_id' := begin rw ←n, simpa using e.right_inv _ end,
  inv_hom_id' := begin
    rw ←e.apply_eq_iff_eq,
    convert ←n _ _,
    convert category.id_comp _ _,
    apply e.right_inv
  end }

lemma coext_equiv_hom_comp {X Y Z : C} {e : Π {Z : C}, (Y ⟶ Z) ≃ (X ⟶ Z)} {n} {f : Y ⟶ Z} :
  (coext_equiv @e n).hom ≫ f = e.to_fun f :=
by convert (n _ _).symm; simp

lemma coext_equiv_hom {X Y : C} {e : Π {Z : C}, (Y ⟶ Z) ≃ (X ⟶ Z)} {n} :
  (coext_equiv @e n).hom = e.to_fun (𝟙 _) := rfl

end


-- TODO: How much of this should be generalized to a possibly large category?
variables (C : Type v) [𝒞 : small_category.{v} C]
include 𝒞

def presheaf := Cᵒᵖ ⥤ Type v

instance presheaf.category : category (presheaf C) := by dunfold presheaf; apply_instance
instance presheaf.has_colimits : has_colimits.{v+1 v} (presheaf C) :=
by dunfold presheaf; apply_instance

variables {C}

section category_of_elements

variables (X : presheaf C)

-- TODO: Implement this as the comma category of `yoneda` over X?
structure category_of_elements :=
(c : C)
(e : yoneda.obj c ⟹ X)

instance category_of_elements.category : category (category_of_elements X) :=
{ hom := λ a b, {f : a.c ⟶ b.c // a.e = (yoneda.map f).vcomp b.e },
  id := λ a, ⟨𝟙 _, by tidy⟩,
  comp := λ a b c f g,
    ⟨f.1 ≫ g.1, begin
       cases f with f hf, cases g with g hg,
       dsimp { iota := tt },
       rw [hf, hg],
       tidy
     end⟩ }

def category_of_elements.forget : category_of_elements X ⥤ C :=
{ obj := λ a, a.c, map := λ a b f, f.1 }

end category_of_elements

section extension
variables {D : Type u} [𝒟 : category.{u v} D] (F : C ⥤ D)
include 𝒟

def restricted_yoneda : D ⥤ Cᵒᵖ ⥤ Type v :=
{ obj := λ d,
  { obj := λ c, F.obj c ⟶ d,
    map := λ c c' f h, F.map f ≫ h,
    map_id' := λ c, by ext h; erw [F.map_id, category.id_comp]; refl,
    map_comp' := λ c c' c'' f f', by ext h; erw [F.map_comp, category.assoc]; refl },
  map := λ d d' g, { app := λ c h, h ≫ g } }

variables [has_colimits.{u v} D]

def yoneda_extension_obj : presheaf C → D :=
λ X, colimit ((category_of_elements.forget X).comp F)

def yoneda_extension_e (X Y) :
  (yoneda_extension_obj F X ⟶ Y) ≃ (X ⟶ (restricted_yoneda F).obj Y) :=
calc
  (colimit _ ⟶ Y)
    ≃ ((category_of_elements.forget X).comp F ⟹ (functor.const _).obj Y)
    : (colimit.universal_property _).equiv
... ≃ { t : Π (c : C) (e : yoneda.obj c ⟹ X), F.obj c ⟶ Y //
        ∀ (c c' : C) (f : c' ⟶ c) (e : yoneda.obj c ⟹ X),
          t c' ((yoneda.map f).vcomp e) = F.map f ≫ t c e }
    : ⟨λ t,
         ⟨λ c e, t.app ⟨c, e⟩,
          λ c d f e, begin
            erw @nat_trans.naturality _ _ _ _ _ _ t ⟨d, yoneda.map f ⊟ e⟩ ⟨c, e⟩ ⟨f, rfl⟩,
            erw category.comp_id
          end⟩,
       λ t,
         { app := λ a, t.1 a.1 a.2,
           naturality' := λ a b f, by erw [f.2, ←t.2 b.1 a.1 f.1 b.2, category.comp_id] },
       λ t, by cases t; ext1 ce; cases ce; refl,
       λ t, by cases t; refl⟩
... ≃ { t : Π (c : C) (e : X.obj c), F.obj c ⟶ Y // _ }
    : equiv.subtype_equiv_of_subtype $ equiv.Pi_congr_right $ λ c,
        equiv.arrow_congr (yoneda_equiv X) (equiv.refl _)
... ≃ { t : Π (c : C) (e : X.obj c), F.obj c ⟶ Y //
        ∀ c c' (f : c ⟶ c'), X.map f ≫ t c' = t c ≫ ((restricted_yoneda F).obj Y).map f }
    : begin
        apply equiv.subtype_equiv_subtype,
        ext t,
        apply forall_congr, intro c,
        apply forall_congr, intro c',
        apply forall_congr, intro f,
        dsimp [equiv.Pi_congr_right, equiv.arrow_congr, equiv.refl, yoneda_equiv],
        split; intro H,
        { ext e,
          have : e = (yoneda_equiv X).to_fun ((yoneda_equiv X).inv_fun e),
            by rw (yoneda_equiv X).right_inv,
          rw this,
          convert H ((yoneda_equiv X).inv_fun e),
          rw ←this,
          simp [yoneda_equiv] },
        { intro e,
          convert congr_fun H ((yoneda_equiv X).to_fun e),
          dsimp [yoneda_equiv],
          convert functor_to_types.naturality _ _ e f (𝟙 c) using 2,
          simp }
      end
... ≃ (X ⟶ (restricted_yoneda F).obj Y)
    : ⟨λ t, { app := t.1, naturality' := λ c c' f, by apply t.2 },
       λ t, ⟨t.app, λ c c' f, by apply t.naturality⟩,
       λ t, by cases t; refl,
       λ t, by cases t; refl⟩

lemma yoneda_extension_e_natural (X Y Y') (g : Y ⟶ Y') (h) :
  (yoneda_extension_e F X Y').to_fun (h ≫ g) =
  (yoneda_extension_e F X Y).to_fun h ≫ (restricted_yoneda F).map g :=
by ext c e; symmetry; apply category.assoc

def yoneda_extension : presheaf C ⥤ D :=
adjunction.left_adjoint_of_equiv (yoneda_extension_e F) (yoneda_extension_e_natural F)

def yoneda_extension_adj : adjunction (yoneda_extension F) (restricted_yoneda F) :=
by apply adjunction.adjunction_of_equiv_left

local attribute [elab_simple] yoneda_extension -- to infer universe parameters
def yoneda_extension_is_extension : yoneda ⋙ yoneda_extension F ≅ F :=
nat_iso.of_components
  (λ c, coext_equiv
     (λ Z, calc
         (F.obj c ⟶ Z)
           ≃ ((restricted_yoneda F).obj Z).obj c           : equiv.refl _
       ... ≃ (yoneda.obj c ⟹ (restricted_yoneda F).obj Z)  : (yoneda_equiv _).symm
       ... ≃ ((yoneda ⋙ yoneda_extension F).obj c ⟶ Z)
           : (yoneda_extension_adj F).hom_equiv.symm)
     begin
       intros d d' f g,
       dsimp [equiv.trans, equiv.symm, equiv.refl],
       rw ←adjunction.hom_equiv_symm_naturality', congr,
       dsimp [yoneda_equiv], ext c', dsimp [restricted_yoneda], simp
     end)
  begin
    intros c c' f,
    dsimp [equiv.trans, equiv.symm, equiv.refl],
    rw [coext_equiv_hom, coext_equiv_hom_comp],
    dsimp, rw ←adjunction.hom_equiv_symm_naturality, congr,
    convert yoneda_equiv_symm_nat f _,
    dsimp [restricted_yoneda], simp
  end

end extension


section canonical_diagram

variables (X : presheaf C)

def restricted_yoneda_yoneda_iso_id : restricted_yoneda yoneda ≅ functor.id (presheaf C) :=
nat_iso.of_components
  (λ X, begin
     fapply nat_iso.of_components,
     { exact λ c, iso_of_equiv (yoneda_equiv X : _ ≃ X.obj c) },
     { intros c c' f, ext t,
       dsimp [iso_of_equiv],
       erw yoneda_equiv_nat, refl }
   end)
  (by intros X Y f; ext c e; refl)

def id_iso_yoneda_extension_yoneda : functor.id (presheaf C) ≅ yoneda_extension yoneda :=
(adjunction.nat_iso_equiv (yoneda_extension_adj _) adjunction.id).inv_fun
  restricted_yoneda_yoneda_iso_id

-- So, we showed that the colimit of the canonical diagram is isomorphic to X, *somehow*!
-- Can we identify the colimit cone as the obvious one?

-- Old stuff below

def canonical_diagram : category_of_elements X ⥤ presheaf C :=
(category_of_elements.forget X).comp yoneda

def canonical_diagram.to_original :
  canonical_diagram X ⟹ (functor.const (category_of_elements X)).obj X :=
{ app := λ a, a.e,
  naturality' := λ a b f, by rw f.2; refl }

def canonical_diagram.cocone : cocone (canonical_diagram X) :=
{ X := X, ι := canonical_diagram.to_original X }

end canonical_diagram

end category_theory
