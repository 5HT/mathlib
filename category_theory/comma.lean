-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Johan Commelin

import category_theory.types
import category_theory.isomorphism
import category_theory.whiskering
import category_theory.opposites
import category_theory.punit

namespace category_theory

universes u₁ v₁ u₂ v₂ u₃ v₃
variables {A : Type u₁} [𝒜 : category.{u₁ v₁} A]
variables {B : Type u₂} [ℬ : category.{u₂ v₂} B]
variables {T : Type u₃} [𝒯 : category.{u₃ v₃} T]
include 𝒜 ℬ 𝒯

structure comma (L : A ⥤ T) (R : B ⥤ T) :=
(left : A . obviously)
(right : B . obviously)
(hom : L.obj left ⟶ R.obj right)

variables {L : A ⥤ T} {R : B ⥤ T}

structure comma_morphism (X Y : comma L R) :=
(left : X.left ⟶ Y.left . obviously)
(right : X.right ⟶ Y.right . obviously)
(w' : L.map left ≫ Y.hom = X.hom ≫ R.map right . obviously)

restate_axiom comma_morphism.w'
attribute [simp] comma_morphism.w

namespace comma_morphism
@[extensionality] lemma ext
  {X Y : comma L R} {f g : comma_morphism X Y}
  (l : f.left = g.left) (r : f.right = g.right) : f = g :=
begin
  cases f, cases g,
  congr; assumption
end
end comma_morphism

instance comma_category : category (comma L R) :=
{ hom := comma_morphism,
  id := λ X,
  { left := 𝟙 X.left,
    right := 𝟙 X.right },
  comp := λ X Y Z f g,
  { left := f.left ≫ g.left,
    right := f.right ≫ g.right,
    w' :=
    begin
      rw [functor.map_comp,
          category.assoc,
          g.w,
          ←category.assoc,
          f.w,
          functor.map_comp,
          category.assoc],
    end }}

namespace comma

section
variables {X Y Z : comma L R} {f : X ⟶ Y} {g : Y ⟶ Z}

@[simp] lemma comp_left  : (f ≫ g).left  = f.left ≫ g.left   := rfl
@[simp] lemma comp_right : (f ≫ g).right = f.right ≫ g.right := rfl

end

variables (L) (R)

def fst : comma L R ⥤ A :=
{ obj := λ X, X.left,
  map := λ _ _ f, f.left }

def snd : comma L R ⥤ B :=
{ obj := λ X, X.right,
  map := λ _ _ f, f.right }

@[simp] lemma fst_obj {X : comma L R} : (fst L R).obj X = X.left := rfl
@[simp] lemma snd_obj {X : comma L R} : (snd L R).obj X = X.right := rfl
@[simp] lemma fst_map {X Y : comma L R} {f : X ⟶ Y} : (fst L R).map f = f.left := rfl
@[simp] lemma snd_map {X Y : comma L R} {f : X ⟶ Y} : (snd L R).map f = f.right := rfl

def nat_trans : fst L R ⋙ L ⟹ snd L R ⋙ R :=
{ app := λ X, X.hom }

section
variables {L₁ L₂ L₃ : A ⥤ T} {R₁ R₂ R₃ : B ⥤ T}

def map_left (l : L₁ ⟹ L₂) : comma L₂ R ⥤ comma L₁ R :=
{ obj := λ X,
  { left  := X.left,
    right := X.right,
    hom   := l.app X.left ≫ X.hom },
  map := λ X Y f,
  { left  := f.left,
    right := f.right,
    w' := by tidy; rw [←category.assoc, l.naturality f.left, category.assoc]; tidy } }

section
variables {X Y : comma L₂ R} {f : X ⟶ Y} {l : L₁ ⟹ L₂}
@[simp] lemma map_left_obj_left  : ((map_left R l).obj X).left  = X.left                := rfl
@[simp] lemma map_left_obj_right : ((map_left R l).obj X).right = X.right               := rfl
@[simp] lemma map_left_obj_hom   : ((map_left R l).obj X).hom   = l.app X.left ≫ X.hom := rfl
@[simp] lemma map_left_map_left  : ((map_left R l).map f).left  = f.left                := rfl
@[simp] lemma map_left_map_right : ((map_left R l).map f).right = f.right               := rfl
end

def map_left_id : map_left R (𝟙 L) ≅ functor.id _ :=
{ hom :=
  { app := λ X, { left := 𝟙 _, right := 𝟙 _ } },
  inv :=
  { app := λ X, { left := 𝟙 _, right := 𝟙 _ } } }

section
variables {X : comma L R}
@[simp] lemma map_left_id_hom_app_left  : (((map_left_id L R).hom).app X).left  = 𝟙 (X.left)  := rfl
@[simp] lemma map_left_id_hom_app_right : (((map_left_id L R).hom).app X).right = 𝟙 (X.right) := rfl
@[simp] lemma map_left_id_inv_app_left  : (((map_left_id L R).inv).app X).left  = 𝟙 (X.left)  := rfl
@[simp] lemma map_left_id_inv_app_right : (((map_left_id L R).inv).app X).right = 𝟙 (X.right) := rfl
end

def map_left_comp (l : L₁ ⟹ L₂) (l' : L₂ ⟹ L₃) :
(map_left R (l ⊟ l')) ≅ (map_left R l') ⋙ (map_left R l) :=
{ hom :=
  { app := λ X, { left := 𝟙 _, right := 𝟙 _ } },
  inv :=
  { app := λ X, { left := 𝟙 _, right := 𝟙 _ } } }

section
variables {X : comma L₃ R} {l : L₁ ⟹ L₂} {l' : L₂ ⟹ L₃}
@[simp] lemma map_left_comp_hom_app_left  : (((map_left_comp R l l').hom).app X).left  = 𝟙 (X.left)  := rfl
@[simp] lemma map_left_comp_hom_app_right : (((map_left_comp R l l').hom).app X).right = 𝟙 (X.right) := rfl
@[simp] lemma map_left_comp_inv_app_left  : (((map_left_comp R l l').inv).app X).left  = 𝟙 (X.left)  := rfl
@[simp] lemma map_left_comp_inv_app_right : (((map_left_comp R l l').inv).app X).right = 𝟙 (X.right) := rfl
end

def map_right (r : R₁ ⟹ R₂) : comma L R₁ ⥤ comma L R₂ :=
{ obj := λ X,
  { left  := X.left,
    right := X.right,
    hom   := X.hom ≫ r.app X.right },
  map := λ X Y f,
  { left  := f.left,
    right := f.right,
    w' := by tidy; rw [←r.naturality f.right, ←category.assoc]; tidy } }

section
variables {X Y : comma L R₁} {f : X ⟶ Y} {r : R₁ ⟹ R₂}
@[simp] lemma map_right_obj_left  : ((map_right L r).obj X).left  = X.left                 := rfl
@[simp] lemma map_right_obj_right : ((map_right L r).obj X).right = X.right                := rfl
@[simp] lemma map_right_obj_hom   : ((map_right L r).obj X).hom   = X.hom ≫ r.app X.right := rfl
@[simp] lemma map_right_map_left  : ((map_right L r).map f).left  = f.left                 := rfl
@[simp] lemma map_right_map_right : ((map_right L r).map f).right = f.right                := rfl
end

def map_right_id : map_right L (𝟙 R) ≅ functor.id _ :=
{ hom :=
  { app := λ X, { left := 𝟙 _, right := 𝟙 _ } },
  inv :=
  { app := λ X, { left := 𝟙 _, right := 𝟙 _ } } }

section
variables {X : comma L R}
@[simp] lemma map_right_id_hom_app_left  : (((map_right_id L R).hom).app X).left  = 𝟙 (X.left)  := rfl
@[simp] lemma map_right_id_hom_app_right : (((map_right_id L R).hom).app X).right = 𝟙 (X.right) := rfl
@[simp] lemma map_right_id_inv_app_left  : (((map_right_id L R).inv).app X).left  = 𝟙 (X.left)  := rfl
@[simp] lemma map_right_id_inv_app_right : (((map_right_id L R).inv).app X).right = 𝟙 (X.right) := rfl
end

def map_right_comp (r : R₁ ⟹ R₂) (r' : R₂ ⟹ R₃) : (map_right L (r ⊟ r')) ≅ (map_right L r) ⋙ (map_right L r') :=
{ hom :=
  { app := λ X, { left := 𝟙 _, right := 𝟙 _ } },
  inv :=
  { app := λ X, { left := 𝟙 _, right := 𝟙 _ } } }

section
variables {X : comma L R₁} {r : R₁ ⟹ R₂} {r' : R₂ ⟹ R₃}
@[simp] lemma map_right_comp_hom_app_left  : (((map_right_comp L r r').hom).app X).left  = 𝟙 (X.left)  := rfl
@[simp] lemma map_right_comp_hom_app_right : (((map_right_comp L r r').hom).app X).right = 𝟙 (X.right) := rfl
@[simp] lemma map_right_comp_inv_app_left  : (((map_right_comp L r r').inv).app X).left  = 𝟙 (X.left)  := rfl
@[simp] lemma map_right_comp_inv_app_right : (((map_right_comp L r r').inv).app X).right = 𝟙 (X.right) := rfl
end

end

end comma

omit 𝒜 ℬ

def over (X : T) := comma.{u₃ v₃ 0 0 u₃ v₃} (functor.id T) (functor.of.obj X)

namespace over

instance {X : T} : category (over X) := by delta over; apply_instance

@[simp] lemma over_right {X : T} (U : over X) : U.right = punit.star := by tidy
@[simp] lemma over_morphism_right {X : T} {U V : over X} (f : U ⟶ V) : f.right = 𝟙 punit.star := by tidy

@[simp] lemma id_left {X : T} (U : over X) : comma_morphism.left (𝟙 U) = 𝟙 U.left := rfl
@[simp] lemma comp_left {X : T} (a b c : over X) (f : a ⟶ b) (g : b ⟶ c) :
  (f ≫ g).left = f.left ≫ g.left := rfl

@[simp] lemma over_w {X : T} {A B : over X} (f : A ⟶ B) : f.left ≫ B.hom = A.hom :=
by have := f.w; tidy

def mk {X Y : T} (f : Y ⟶ X) : over X :=
{ left := Y, hom := f }

@[simp] lemma mk_left {X Y : T} (f : Y ⟶ X) : (mk f).left = Y := rfl
@[simp] lemma mk_hom {X Y : T} (f : Y ⟶ X) : (mk f).hom = f := rfl

def forget {X : T} : (over X) ⥤ T := comma.fst _ _

@[simp] lemma forget_obj {X : T} {U : over X} : forget.obj U = U.left := rfl
@[simp] lemma forget_map {X : T} {U V : over X} {f : U ⟶ V} : forget.map f = f.left := rfl

def map {X Y : T} (f : X ⟶ Y) : over X ⥤ over Y := comma.map_right _ $ functor.of.map f

section
variables {X Y : T} {f : X ⟶ Y} {U V : over X} {g : U ⟶ V}
@[simp] lemma map_obj_left : ((map f).obj U).left = U.left := rfl
@[simp] lemma map_obj_hom  : ((map f).obj U).hom  = U.hom ≫ f := rfl
@[simp] lemma map_map_left : ((map f).map g).left = g.left := rfl
end

end over

def under (X : T) := comma.{0 0 u₃ v₃ u₃ v₃} (functor.of.obj X) (functor.id T)

namespace under

instance {X : T} : category (under X) := by delta under; apply_instance

@[simp] lemma under_left {X : T} (U : under X) : U.left = punit.star := by tidy
@[simp] lemma under_morphism_left {X : T} {U V : under X} (f : U ⟶ V) : f.left = 𝟙 punit.star := by tidy

@[simp] lemma id_left {X : T} (U : under X) : comma_morphism.left (𝟙 U) = 𝟙 U.left := rfl
@[simp] lemma comp_left {X : T} (a b c : under X) (f : a ⟶ b) (g : b ⟶ c) :
  (f ≫ g).left = f.left ≫ g.left := rfl

@[simp] lemma under_w {X : T} {A B : under X} (f : A ⟶ B) : A.hom ≫ f.right = B.hom :=
by have := f.w; tidy

def mk {X Y : T} (f : X ⟶ Y) : under X :=
{ right := Y, hom := f }

@[simp] lemma mk_right {X Y : T} (f : X ⟶ Y) : (mk f).right = Y := rfl
@[simp] lemma mk_hom {X Y : T} (f : X ⟶ Y) : (mk f).hom = f := rfl

def forget {X : T} : (under X) ⥤ T := comma.snd _ _

@[simp] lemma forget_obj {X : T} {U : under X} : forget.obj U = U.right := rfl
@[simp] lemma forget_map {X : T} {U V : under X} {f : U ⟶ V} : forget.map f = f.right := rfl

def map {X Y : T} (f : X ⟶ Y) : under Y ⥤ under X := comma.map_left _ $ functor.of.map f

section
variables {X Y : T} {f : X ⟶ Y} {U V : under Y} {g : U ⟶ V}
@[simp] lemma map_obj_right : ((map f).obj U).right = U.right := rfl
@[simp] lemma map_obj_hom   : ((map f).obj U).hom   = f ≫ U.hom := rfl
@[simp] lemma map_map_right : ((map f).map g).right = g.right := rfl
end

end under

end category_theory
