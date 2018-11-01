/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Chris Hughes, Morenikeji Neri
-/

import algebra.euclidean_domain
import ring_theory.ideals ring_theory.noetherian ring_theory.unique_factorization_domain

variables {α : Type*}

open set function ideal
local attribute [instance] classical.prop_decidable

class is_principal_ideal [comm_ring α] (S : set α) : Prop :=
(principal : ∃ a : α, S = {x | a ∣ x})

class principal_ideal_domain (α : Type*) extends integral_domain α :=
(principal : ∀ (S : ideal α), is_principal_ideal (S : set α))

namespace is_principal_ideal
variable [comm_ring α]

noncomputable def generator (S : set α) [is_principal_ideal S] : α :=
classical.some (principal S)

lemma generator_generates (S : set α) [is_principal_ideal S] : {x | generator S ∣ x} = S :=
eq.symm (classical.some_spec (principal S))

@[simp] lemma generator_mem (S : set α) [is_principal_ideal S] : generator S ∈ S :=
by conv {to_rhs, rw ← generator_generates S}; exact dvd_refl _

lemma mem_iff_generator_dvd (S : set α) [is_principal_ideal S] {x : α} : x ∈ S ↔ generator S ∣ x :=
by conv {to_lhs, rw ← generator_generates S}; refl

lemma eq_bot_iff_generator_eq_zero (S : set α) [is_principal_ideal S] :
  S = (⊥ : ideal α) ↔ generator S = 0 :=
⟨λ h, by rw [← submodule.mem_bot, ← submodule.mem_coe, ← h]; exact generator_mem S,
  λ h, set.ext $ λ x, by rw [mem_iff_generator_dvd S, h, zero_dvd_iff, submodule.mem_coe, submodule.mem_bot]⟩

def to_ideal (S : set α) [is_principal_ideal S] : ideal α :=
{ carrier := S,
  zero := by rw ← generator_generates S; simp,
  add := λ x y h, by rw ← generator_generates S at *; exact (dvd_add_iff_right h).1,
  smul := λ c x h, by rw ← generator_generates S at h ⊢; exact dvd_mul_of_dvd_right h _ }

end is_principal_ideal

namespace is_prime
open is_principal_ideal ideal

lemma to_maximal_ideal [principal_ideal_domain α] {S : ideal α}
  [hpi : is_prime S] (hS : S ≠ ⊥) : is_maximal S :=
is_maximal_iff.2 ⟨(ne_top_iff_one S).1 hpi.1, begin
  assume T x hST hxS hxT,
  haveI := principal_ideal_domain.principal S,
  haveI := principal_ideal_domain.principal T,
  cases (mem_iff_generator_dvd _).1 (hST ((mem_iff_generator_dvd _).2 (dvd_refl _))) with z hz,
  cases hpi.2 (show generator ↑T * z ∈ S,
    by rw [← submodule.mem_coe, mem_iff_generator_dvd ↑S, ← hz]),
  { have hST' : S = T := submodule.ext' (set.subset.antisymm hST
      (λ y hyT, (mem_iff_generator_dvd _).2
        (dvd.trans ((mem_iff_generator_dvd _).1 h) ((mem_iff_generator_dvd _).1 hyT)))),
    rw hST' at hxS,
    exact (hxS hxT).elim },
  { cases (mem_iff_generator_dvd ↑S).1 h with y hy,
    have : generator ↑S ≠ (0:α) :=
      mt (submodule.ext' ∘ (eq_bot_iff_generator_eq_zero _).2) hS,
    rw [← mul_one (generator (↑S : set α)), hy, mul_left_comm,
      domain.mul_left_inj this] at hz,
    exact hz.symm ▸ ideal.mul_mem_right _ (generator_mem ↑T) }
end⟩

end is_prime

section
open euclidean_domain
variable [euclidean_domain α]

lemma mod_mem_iff {S : ideal α} {x y : α} (hy : y ∈ S) : x % y ∈ S ↔ x ∈ S :=
⟨λ hxy, div_add_mod x y ▸ ideal.add_mem S (mul_mem_right S hy) hxy,
  λ hx, (mod_eq_sub_mul_div x y).symm ▸ ideal.sub_mem S hx (ideal.mul_mem_right S hy)⟩

instance euclidean_domain.to_principal_ideal_domain : principal_ideal_domain α :=
{ principal := λ S, by exactI
    ⟨if h : {x : α | x ∈ S ∧ x ≠ 0} = ∅
    then ⟨0, set.ext $ λ a, ⟨λ haS, zero_dvd_iff.2 $ by_contradiction $ λ ha0,
              ((ext_iff _ _).1 h a).1 ⟨haS, ha0⟩,
            λ h₁, (show a = 0, by simpa using h₁).symm ▸ ideal.zero_mem S⟩⟩
    else
    have wf : well_founded euclidean_domain.r := euclidean_domain.r_well_founded α,
    have hmin : well_founded.min wf {x : α | x ∈ S ∧ x ≠ 0} h ∈ S ∧
        well_founded.min wf {x : α | x ∈ S ∧ x ≠ 0} h ≠ 0,
      from well_founded.min_mem wf {x : α | x ∈ S ∧ x ≠ 0} h,
    ⟨well_founded.min wf {x : α | x ∈ S ∧ x ≠ 0} h,
      set.ext $ λ x,
      ⟨λ hx, div_add_mod x (well_founded.min wf {x : α | x ∈ S ∧ x ≠ 0} h) ▸
        dvd_add (dvd_mul_right _ _)
        (have (x % (well_founded.min wf {x : α | x ∈ S ∧ x ≠ 0} h) ∉ {x : α | x ∈ S ∧ x ≠ 0}),
          from λ h₁, well_founded.not_lt_min wf _ h h₁ (mod_lt x hmin.2),
        have x % well_founded.min wf {x : α | x ∈ S ∧ x ≠ 0} h = 0, by finish [(mod_mem_iff hmin.1).2 hx],
        by simp *),
      λ hx, let ⟨y, hy⟩ := hx in hy.symm ▸ ideal.mul_mem_right _ hmin.1⟩⟩⟩ }

end


namespace principal_ideal_domain
variables [principal_ideal_domain α]

lemma is_noetherian_ring : is_noetherian_ring α :=
assume s : ideal α,
begin
  cases (principal s).principal with a hs,
  refine ⟨finset.singleton a, submodule.ext' _⟩, rw hs, ext x,
  change x ∈ span ({a}:set α) ↔ ∃ _, _,
  rw mem_span_singleton,
  exact exists_congr (λ _, by rw [eq_comm, mul_comm])
end

section
local attribute [instance] classical.prop_decidable
open submodule

lemma factors_decreasing (b₁ b₂ : α) (h₁ : b₁ ≠ 0) (h₂ : ¬ is_unit b₂) :
  submodule.span {b₁} > submodule.span ({b₁ * b₂} : set α) :=
lt_of_le_not_le (ideal.span_le.2 $ singleton_subset_iff.2 $
  ideal.mem_span_singleton.2 ⟨b₂, by rw mul_comm⟩) $ λ h,
have _ := singleton_subset_iff.1 $ ideal.span_le.1 h,
let ⟨c, hc⟩ := ideal.mem_span_singleton.1 this in
have b₂ * c = 1, from eq_of_mul_eq_mul_left h₁
  (by rwa [mul_one, ← mul_assoc, mul_comm]),
h₂ ⟨units.mk_of_mul_eq_one _ c this, rfl⟩

lemma exists_factors (a : α) : a ≠ 0 → ∃f:multiset α, (∀b∈f, irreducible b) ∧ associated a f.prod :=
have well_founded (inv_image (>) (λb, submodule.span ({b} : set α))), from
  inv_image.wf _ $ is_noetherian_iff_well_founded.1 $ is_noetherian_ring,
this.induction a
begin
  assume a ih ha,
  by_cases h_unit : is_unit a,
  { exact match a, h_unit with _, ⟨u, rfl⟩ := ⟨∅, by simp, u⁻¹, by simp⟩ end },
  by_cases h_irreducible : irreducible a,
  { exact ⟨{a}, by simp [h_irreducible]⟩ },

  have : ∃b₁ b₂, a = b₁ * b₂ ∧ ¬ is_unit b₁ ∧ ¬ is_unit b₂,
  { simp [irreducible, not_or_distrib, not_forall] at h_irreducible; from h_irreducible h_unit },
  rcases this with ⟨b₁, b₂, eq, h₁, h₂⟩,

  have hb₁ : b₁ ≠ 0, { assume eq, simp * at * },
  have : submodule.span {b₁} > submodule.span ({a} : set α),
    by rw [eq]; from factors_decreasing b₁ b₂ hb₁ h₂,
  rcases ih b₁ this hb₁ with ⟨f₁, hf₁, ha₁⟩,

  have hb₂ : b₂ ≠ 0, { assume eq, simp * at * },
  have : submodule.span {b₂} > submodule.span ({a} : set α),
    by rw [eq, mul_comm]; from factors_decreasing b₂ b₁ hb₂ h₁,
  rcases ih b₂ this hb₂ with ⟨f₂, hf₂, ha₂⟩,

  refine ⟨f₁ + f₂, _⟩,
  simpa [or_imp_distrib, forall_and_distrib, eq, associated_mul_mul ha₁ ha₂] using and.intro hf₁ hf₂
end

end

lemma is_maximal_ideal_of_irreducible {p : α} (hp : irreducible p) :
  is_maximal (@is_principal_ideal.to_ideal α _ {a | p ∣ a} ⟨⟨p, rfl⟩⟩) :=
is_maximal_iff.2 ⟨λ ⟨q, hq⟩, hp.1 ⟨units.mk_of_mul_eq_one _ q hq.symm, rfl⟩, begin
  assume T x hT hxp hx,
  cases (principal T).principal with q hq,
  have := hT (dvd_refl p), rw hq at this,
  cases this with c hc, rw hc at hp,
  rw [← submodule.mem_coe, hq] at hx ⊢,
  rcases hp.2 _ _ rfl with ⟨q, rfl⟩ | ⟨c, rfl⟩,
  { exact units.coe_dvd _ _ },
  { cases hx with y hy,
    exact (hxp ⟨(c⁻¹ : units α) * y, by rwa [hc, ← mul_assoc,
      mul_assoc q, ← units.coe_mul, mul_inv_self, units.coe_one, mul_one]⟩).elim }
end⟩

lemma prime_of_irreducible {p : α} (hp : irreducible p) : prime p :=
have is_prime {a | p ∣ a}, from
  @is_maximal_ideal.is_prime_ideal α _ _ (is_maximal_ideal_of_irreducible hp),
⟨assume h, not_irreducible_zero (show irreducible (0:α), from h ▸ hp), hp.1, this.mem_or_mem_of_mul_mem⟩

lemma associates_prime_of_irreducible : ∀{p : associates α}, irreducible p → p.prime :=
associates.forall_associated.2 $ assume a,
begin
  rw [associates.irreducible_mk_iff, associates.prime_mk],
  exact prime_of_irreducible
end

lemma eq_of_prod_eq_associates {s : multiset (associates α)} :
  ∀{t:multiset (associates α)}, (∀a∈s, irreducible a) → (∀a∈t, irreducible a) → s.prod = t.prod →
  s = t :=
begin
  letI := classical.dec_eq (associates α),
  refine s.induction_on _ _,
  { assume t _ ht eq,
    have : ∀a∈t, (a:associates α) = 1, from associates.prod_eq_one_iff.1 eq.symm,
    have : ∀a∈t, irreducible (1 : associates α), from assume a ha, this a ha ▸ ht a ha,
    exact (multiset.eq_zero_of_forall_not_mem $ assume a ha, not_irreducible_one $ this a ha).symm },
  { assume a s ih t hs ht h,
    have ha : a.prime, from associates_prime_of_irreducible (hs a $ multiset.mem_cons_self a s),
    rcases associates.exists_mem_multiset_le_of_prime ha ⟨s.prod, by simpa using h⟩
      with ⟨x, hx, hxa⟩,
    have : x.prime, from associates_prime_of_irreducible (ht x hx),
    have : a = x := (associates.one_or_eq_of_le_of_prime _ _ this hxa).resolve_left ha.2.1,
    subst this,
    have : s.prod = (t.erase a).prod,
    { rw ← multiset.cons_erase hx at h,
      simp at h,
      exact associates.eq_of_mul_eq_mul_left a _ _ ha.1 h },
    have : s = t.erase a, from ih
      (assume x hxs, hs x $ multiset.mem_cons_of_mem hxs)
      (assume x hxt, ht x $ classical.by_cases
        (assume h : x = a, h.symm ▸ hx)
        (assume ne, (multiset.mem_erase_of_ne ne).1 hxt))
      this,
    rw [this, multiset.cons_erase hx] }
end

lemma associated_of_associated_prod_prod {s t : multiset α}
  (hs : ∀a∈s, irreducible a) (ht : ∀a∈t, irreducible a) (h : associated s.prod t.prod) :
  multiset.rel associated s t :=
begin
  refine (associates.rel_associated_iff_map_eq_map.2 $ eq_of_prod_eq_associates _ _ _),
  { assume a ha,
    rcases multiset.mem_map.1 ha with ⟨x, hx, rfl⟩,
    simpa [associates.irreducible_mk_iff] using hs x hx },
  { assume a ha,
    rcases multiset.mem_map.1 ha with ⟨x, hx, rfl⟩,
    simpa [associates.irreducible_mk_iff] using ht x hx },
  rwa [associates.prod_mk, associates.prod_mk, associates.mk_eq_mk_iff_associated]
end

section
local attribute [instance] classical.prop_decidable

noncomputable def factors (a : α) : multiset α :=
if h : a = 0 then ∅ else classical.some (exists_factors a h)

lemma factors_spec (a : α) (h : a ≠ 0) :
  (∀b∈factors a, irreducible b) ∧ associated a (factors a).prod :=
begin
  unfold factors, rw [dif_neg h],
  exact classical.some_spec (exists_factors a h)
end

/-- The unique factorization domain structure given by the principal ideal domain.

This is not added as type class instance, since the `factors` might be computed in a different way.
E.g. factors could return normalized values.
-/
noncomputable def to_unique_factorization_domain : unique_factorization_domain α :=
{ factors := factors,
  factors_prod := assume a ha, associated.symm (factors_spec a ha).2,
  irreducible_factors := assume a ha, (factors_spec a ha).1,
  unique := assume s t, associated_of_associated_prod_prod }

end

end principal_ideal_domain
