/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Andreas Swerdlow 
-/

import algebra.module ring_theory.ring_hom_isom_invo

open module ring ring_invo

class sesquilinear_form_space (R : Type*) (V : Type*) [ring R] (Hi : ring_invo R) extends module R V := 
(sesq_form : V → V → R)
(fst_add_lin : ∀ (x y z : V), sesq_form (x + y) z = sesq_form x z + sesq_form y z)
(fst_mul_lin : ∀ (x y : V) (a : R), sesq_form (a • x) y = a * (sesq_form x y))
(snd_add_lin : ∀ (x y z : V), sesq_form x (y + z) = sesq_form x y + sesq_form x z)
(snd_mul_antilin : ∀ (a : R) (x y : V), sesq_form x (a • y) = (invo Hi a) * (sesq_form x y))  

namespace sesquilinear_form_space

open sesquilinear_form_space

variables {R : Type*} [ring R] {V : Type*} (Hi : ring_invo R) [sesquilinear_form_space R V Hi]

lemma zero_sesq (x : V) :
sesq_form Hi 0 x = 0 := by rw [←zero_smul, fst_mul_lin, ring.zero_mul]; exact 0

lemma sesq_zero (x : V) :
sesq_form Hi x 0 = 0 := by rw [←zero_smul, snd_mul_antilin, invo_zero, ring.zero_mul]; exact 0

lemma sesq_neg_left (x y : V) : 
sesq_form Hi (-x) y = -(sesq_form Hi x y : R) := by rw [←neg_one_smul, fst_mul_lin, neg_one_mul]

lemma sesq_neg_right (x y : V) : 
sesq_form Hi x (-y) = -(sesq_form Hi x y) := by rw [←neg_one_smul, snd_mul_antilin, invo_neg, ring_invo.map_one, neg_one_mul]

lemma sesq_sub_left (x y z : V) :
sesq_form Hi (x - y) z = sesq_form Hi x z - sesq_form Hi y z := by rw [sub_eq_add_neg, fst_add_lin, sesq_neg_left]; refl

lemma sesq_sub_right (x y z : V) :
sesq_form Hi x (y - z) = sesq_form Hi x y - sesq_form Hi x z := by rw [sub_eq_add_neg, snd_add_lin, sesq_neg_right]; refl

def is_ortho (x y : V) : Prop :=
sesq_form Hi x y = 0

lemma ortho_zero (x : V) : 
is_ortho Hi 0 x := zero_sesq Hi x 

theorem ortho_mul_left {D : Type*} [domain D] (Hi : ring_invo D) [sesquilinear_form_space D V Hi] (x y : V) (a : D) (ha : a ≠ 0) : 
(is_ortho Hi x y) ↔ (is_ortho Hi (a • x) y) :=
begin
dunfold is_ortho,
split,
    intros H,
    rw [fst_mul_lin, H, ring.mul_zero],

    intros H,
    rw [fst_mul_lin, mul_eq_zero] at H,
    cases H, 
        trivial, 

        exact H, 
end

theorem ortho_mul_right {D : Type*} [domain D] (Hi : ring_invo D) [sesquilinear_form_space D V Hi] (x y : V) (a : D) (ha : a ≠ 0) : 
(is_ortho Hi x y) ↔ (is_ortho Hi x (a • y)) :=
begin
dunfold is_ortho,
split,
    intros H,
    rw [snd_mul_antilin, H, ring.mul_zero],

    intros H,
    rw [snd_mul_antilin, mul_eq_zero] at H,
    cases H,
        rw invo_zero_iff at H, 
        trivial, 

        exact H, 
end

end sesquilinear_form_space

class reflx_sesquilinear_form_space (R : Type*) (V : Type*) [ring R] (Hi : ring_invo R) extends sesquilinear_form_space R V Hi := 
(is_reflx : ∀ {x y : V}, sesq_form x y = 0 → sesq_form y x = 0)

namespace reflx_sesquilinear_form_space

open reflx_sesquilinear_form_space sesquilinear_form_space

lemma ortho_sym {R : Type*} {V : Type*} [ring R] (Hi : ring_invo R) [reflx_sesquilinear_form_space R V Hi] (x y : V) : 
is_ortho Hi x y ↔ is_ortho Hi y x := ⟨λ H, is_reflx H, λ H, is_reflx H⟩

end reflx_sesquilinear_form_space

class sym_sesquilinear_form_space (R : Type*) (V : Type*) [ring R] (Hi : ring_invo R) extends sesquilinear_form_space R V Hi := 
(is_invo_sym : ∀ (x y : V), sesq_form x y = invo Hi (sesq_form y x))

namespace sym_sesquilinear_form_space

open sym_sesquilinear_form_space sesquilinear_form_space

instance reflx_sesquilinear_form_space (R : Type*) (V : Type*) [ring R] (Hi : ring_invo R) [sym_sesquilinear_form_space R V Hi] : 
reflx_sesquilinear_form_space R V Hi :=
⟨λ x y H, (invo_zero_iff Hi).mp ((is_invo_sym Hi x y) ▸ (H))⟩ 

def ortho_sym {R : Type*} {V : Type*} [ring R] (Hi : ring_invo R) [sym_sesquilinear_form_space R V Hi] (x y : V) : 
is_ortho Hi x y ↔ is_ortho Hi y x := reflx_sesquilinear_form_space.ortho_sym Hi x y

end sym_sesquilinear_form_space
