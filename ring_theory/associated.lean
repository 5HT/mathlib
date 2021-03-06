/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker

Associated and irreducible elements.
-/
import order.galois_connection algebra.group data.equiv.basic data.multiset data.int.gcd

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
open lattice

/-- is unit -/
def is_unit [monoid α] (a : α) : Prop := ∃u:units α, a = u

@[simp] theorem is_unit_zero_iff [semiring α] : is_unit (0 : α) ↔ (0:α) = 1 :=
⟨λ ⟨⟨_, a, (a0 : 0 * a = 1), _⟩, rfl⟩, by rwa zero_mul at a0,
 λ h, begin
  haveI := subsingleton_of_zero_eq_one _ h,
  refine ⟨⟨0, 0, _, _⟩, rfl⟩; apply subsingleton.elim
 end⟩

@[simp] theorem not_is_unit_zero [nonzero_comm_ring α] : ¬ is_unit (0 : α) :=
mt is_unit_zero_iff.1 zero_ne_one

@[simp] theorem is_unit_one [monoid α] : is_unit (1:α) := ⟨1, rfl⟩

theorem is_unit_of_mul_one [comm_monoid α] (a b : α) (h : a * b = 1) : is_unit a :=
⟨units.mk_of_mul_eq_one a b h, rfl⟩

theorem is_unit_iff_exists_inv [comm_monoid α] {a : α} : is_unit a ↔ ∃ b, a * b = 1 :=
⟨by rintro ⟨⟨a, b, hab, _⟩, rfl⟩; exact ⟨b, hab⟩,
 λ ⟨b, hab⟩, is_unit_of_mul_one _ b hab⟩

theorem is_unit_iff_exists_inv' [comm_monoid α] {a : α} : is_unit a ↔ ∃ b, b * a = 1 :=
by simp [is_unit_iff_exists_inv, mul_comm]

lemma is_unit_pow [monoid α] {a : α} (n : ℕ) : is_unit a → is_unit (a ^ n) :=
λ ⟨u, hu⟩, ⟨u ^ n, by simp *⟩

@[simp] theorem units.is_unit_mul_units [monoid α] (a : α) (u : units α) :
  is_unit (a * u) ↔ is_unit a :=
iff.intro
  (assume ⟨v, hv⟩,
    have is_unit (a * ↑u * ↑u⁻¹), by existsi v * u⁻¹; rw [hv, units.coe_mul],
    by rwa [mul_assoc, units.mul_inv, mul_one] at this)
  (assume ⟨v, hv⟩, hv.symm ▸ ⟨v * u, (units.coe_mul v u).symm⟩)

theorem is_unit_of_mul_is_unit_left {α} [comm_monoid α] {x y : α}
  (hu : is_unit (x * y)) : is_unit x :=
let ⟨z, hz⟩ := is_unit_iff_exists_inv.1 hu in
is_unit_iff_exists_inv.2 ⟨y * z, by rwa ← mul_assoc⟩

theorem is_unit_of_mul_is_unit_right {α} [comm_monoid α] {x y : α}
  (hu : is_unit (x * y)) : is_unit y :=
@is_unit_of_mul_is_unit_left _ _ y x $ by rwa mul_comm

theorem is_unit_iff_dvd_one [comm_semiring α] {x : α} : is_unit x ↔ x ∣ 1 :=
⟨by rintro ⟨u, rfl⟩; exact ⟨_, u.mul_inv.symm⟩,
 λ ⟨y, h⟩, ⟨⟨x, y, h.symm, by rw [h, mul_comm]⟩, rfl⟩⟩

theorem is_unit_iff_forall_dvd [comm_semiring α] {x : α} :
  is_unit x ↔ ∀ y, x ∣ y :=
is_unit_iff_dvd_one.trans ⟨λ h y, dvd.trans h (one_dvd _), λ h, h _⟩

theorem mul_dvd_of_is_unit_left [comm_semiring α] {x y z : α} (h : is_unit x) : x * y ∣ z ↔ y ∣ z :=
⟨dvd_trans (dvd_mul_left _ _),
 dvd_trans $ by simpa using mul_dvd_mul_right (is_unit_iff_dvd_one.1 h) y⟩

theorem mul_dvd_of_is_unit_right [comm_semiring α] {x y z : α} (h : is_unit y) : x * y ∣ z ↔ x ∣ z :=
by rw [mul_comm, mul_dvd_of_is_unit_left h]

theorem is_unit_of_dvd_unit {α} [comm_semiring α] {x y : α}
  (xy : x ∣ y) (hu : is_unit y) : is_unit x :=
is_unit_iff_dvd_one.2 $ dvd_trans xy $ is_unit_iff_dvd_one.1 hu

@[simp] theorem is_unit_nat {n : ℕ} : is_unit n ↔ n = 1 :=
iff.intro
  (assume ⟨u, hu⟩, match n, u, hu, nat.units_eq_one u with _, _, rfl, rfl := rfl end)
  (assume h, h.symm ▸ ⟨1, rfl⟩)

theorem is_unit_int {n : ℤ} : is_unit n ↔ n.nat_abs = 1 :=
⟨λ ⟨u, hu⟩, (int.units_eq_one_or u).elim (by simp *) (by simp *),
  λ h, is_unit_iff_dvd_one.2 ⟨n, by rw [← int.nat_abs_mul_self, h]; refl⟩⟩

lemma is_unit_of_dvd_one [comm_semiring α] : ∀a ∣ 1, is_unit (a:α)
| a ⟨b, eq⟩ := ⟨units.mk_of_mul_eq_one a b eq.symm, rfl⟩

/-- prime element of a semiring -/
def prime [comm_semiring α] (p : α) : Prop :=
p ≠ 0 ∧ ¬ is_unit p ∧ (∀a b, p ∣ a * b → p ∣ a ∨ p ∣ b)

lemma not_prime_zero [integral_domain α] : ¬ prime (0 : α)
| ⟨h, _⟩ := h rfl

@[simp] lemma not_prime_one [comm_semiring α] : ¬ prime (1 : α) :=
λ h, h.2.1 is_unit_one

lemma exists_mem_multiset_dvd_of_prime [comm_semiring α] {s : multiset α} {p : α} (hp : prime p) :
  p ∣ s.prod → ∃a∈s, p ∣ a :=
multiset.induction_on s (assume h, (hp.2.1 $ is_unit_of_dvd_one _ h).elim) $
assume a s ih h,
  have p ∣ a * s.prod, by simpa using h,
  match hp.2.2 a s.prod this with
  | or.inl h := ⟨a, multiset.mem_cons_self a s, h⟩
  | or.inr h := let ⟨a, has, h⟩ := ih h in ⟨a, multiset.mem_cons_of_mem has, h⟩
  end

/-- `irreducible p` states that `p` is non-unit and only factors into units.

We explicitly avoid stating that `p` is non-zero, this would require a semiring. Assuming only a
monoid allows us to reuse irreducible for associated elements.
-/
@[class] def irreducible [monoid α] (p : α) : Prop :=
¬ is_unit p ∧ ∀a b, p = a * b → is_unit a ∨ is_unit b

@[simp] theorem not_irreducible_one [monoid α] : ¬ irreducible (1 : α) :=
by simp [irreducible]

@[simp] theorem not_irreducible_zero [semiring α] : ¬ irreducible (0 : α)
| ⟨hn0, h⟩ := have is_unit (0:α) ∨ is_unit (0:α), from h 0 0 ((mul_zero 0).symm),
  this.elim hn0 hn0

theorem nonzero_of_irreducible [semiring α] : ∀ {p:α}, irreducible p → p ≠ 0
| _ hp rfl := not_irreducible_zero hp

theorem of_irreducible_mul {α} [monoid α] {x y : α} :
  irreducible (x * y) → is_unit x ∨ is_unit y
| ⟨_, h⟩ := h _ _ rfl

theorem irreducible_or_factor {α} [monoid α] (x : α) (h : ¬ is_unit x) :
  irreducible x ∨ ∃ a b, ¬ is_unit a ∧ ¬ is_unit b ∧ a * b = x :=
begin
  haveI := classical.dec,
  refine or_iff_not_imp_right.2 (λ H, _),
  simp [h, irreducible] at H ⊢,
  refine λ a b h, classical.by_contradiction $ λ o, _,
  simp [not_or_distrib] at o,
  exact H _ o.1 _ o.2 h.symm
end

theorem irreducible_iff_nat_prime : ∀(a : ℕ), irreducible a ↔ nat.prime a
| 0 := by simp [nat.not_prime_zero]
| 1 := by simp [nat.prime, one_lt_two]
| (n + 2) :=
  have h₁ : ¬n + 2 = 1, from dec_trivial,
  begin
    simp [h₁, nat.prime, irreducible, (≥), nat.le_add_left 2 n, (∣)],
    refine forall_congr (assume a, forall_congr $ assume b, forall_congr $ assume hab, _),
    by_cases a = 1; simp [h],
    split,
    { assume hb, simpa [hb] using hab.symm },
    { assume ha, subst ha,
      have : n + 2 > 0, from dec_trivial,
      refine nat.eq_of_mul_eq_mul_left this _,
      rw [← hab, mul_one] }
  end

lemma nat.prime_iff_prime {p : ℕ} : p.prime ↔ _root_.prime (p : ℕ) :=
⟨λ hp, ⟨nat.pos_iff_ne_zero.1 hp.pos, mt is_unit_iff_dvd_one.1 hp.not_dvd_one,
    λ a b, hp.dvd_mul.1⟩,
  λ hp, ⟨nat.one_lt_iff_ne_zero_and_ne_one.2 ⟨hp.1, λ h1, hp.2.1 $ h1.symm ▸ is_unit_one⟩,
    λ a h, let ⟨b, hab⟩ := h in
      (hp.2.2 a b (hab ▸ dvd_refl _)).elim
        (λ ha, or.inr (nat.dvd_antisymm h ha))
        (λ hb, or.inl (have hpb : p = b, from nat.dvd_antisymm hb
            (hab.symm ▸ dvd_mul_left _ _),
          (nat.mul_left_inj (show 0 < p, from
              nat.pos_of_ne_zero hp.1)).1 $
            by rw [hpb, mul_comm, ← hab, hpb, mul_one]))⟩⟩

lemma nat.prime_iff_prime_int {p : ℕ} : p.prime ↔ _root_.prime (p : ℤ) :=
⟨λ hp, ⟨int.coe_nat_ne_zero_iff_pos.2 hp.pos, mt is_unit_int.1 hp.ne_one,
  λ a b h, by rw [← int.dvd_nat_abs, int.coe_nat_dvd, int.nat_abs_mul, hp.dvd_mul] at h;
    rwa [← int.dvd_nat_abs, int.coe_nat_dvd, ← int.dvd_nat_abs, int.coe_nat_dvd]⟩,
  λ hp, nat.prime_iff_prime.2 ⟨int.coe_nat_ne_zero.1 hp.1,
      mt is_unit_nat.1 $ λ h, by simpa [h, not_prime_one] using hp,
    λ a b, by simpa only [int.coe_nat_dvd, (int.coe_nat_mul _ _).symm] using hp.2.2 a b⟩⟩

lemma irreducible_of_prime [integral_domain α] {p : α} (hp : prime p) : irreducible p :=
⟨hp.2.1, λ a b hab,
  (show a * b ∣ a ∨ a * b ∣ b, from hab ▸ hp.2.2 a b (hab ▸ (dvd_refl _))).elim
    (λ ⟨x, hx⟩, or.inr (is_unit_iff_dvd_one.2
      ⟨x, (domain.mul_left_inj (show a ≠ 0, from λ h, by simp [*, prime] at *)).1
        $ by conv {to_lhs, rw hx}; simp [mul_comm, mul_assoc, mul_left_comm]⟩))
    (λ ⟨x, hx⟩, or.inl (is_unit_iff_dvd_one.2
      ⟨x, (domain.mul_left_inj (show b ≠ 0, from λ h, by simp [*, prime] at *)).1
        $ by conv {to_lhs, rw hx}; simp [mul_comm, mul_assoc, mul_left_comm]⟩))⟩

lemma succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul [integral_domain α] {p : α} (hp : prime p) {a b : α}
  {k l : ℕ} : p ^ k ∣ a → p ^ l ∣ b → p ^ ((k + l) + 1) ∣ a * b →
  p ^ (k + 1) ∣ a ∨ p ^ (l + 1) ∣ b :=
λ ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩,
have h : p ^ (k + l) * (x * y) = p ^ (k + l) * (p * z),
  by simpa [mul_comm, _root_.pow_add, hx, hy, mul_assoc, mul_left_comm] using hz,
have hp0: p ^ (k + l) ≠ 0, from pow_ne_zero _ hp.1,
have hpd : p ∣ x * y, from ⟨z, by rwa [domain.mul_left_inj hp0] at h⟩,
(hp.2.2 x y hpd).elim
  (λ ⟨d, hd⟩, or.inl ⟨d, by simp [*, _root_.pow_succ, mul_comm, mul_left_comm, mul_assoc]⟩)
  (λ ⟨d, hd⟩, or.inr ⟨d, by simp [*, _root_.pow_succ, mul_comm, mul_left_comm, mul_assoc]⟩)

def associated [monoid α] (x y : α) : Prop := ∃u:units α, x * u = y

local infix ` ~ᵤ ` : 50 := associated

namespace associated

@[refl] protected theorem refl [monoid α] (x : α) : x ~ᵤ x := ⟨1, by simp⟩

@[symm] protected theorem symm [monoid α] : ∀{x y : α}, x ~ᵤ y → y ~ᵤ x
| x _ ⟨u, rfl⟩ := ⟨u⁻¹, by rw [mul_assoc, units.mul_inv, mul_one]⟩

@[trans] protected theorem trans [monoid α] : ∀{x y z : α}, x ~ᵤ y → y ~ᵤ z → x ~ᵤ z
| x _ _ ⟨u, rfl⟩ ⟨v, rfl⟩ := ⟨u * v, by rw [units.coe_mul, mul_assoc]⟩

protected def setoid (α : Type*) [monoid α] : setoid α :=
{ r := associated, iseqv := ⟨associated.refl, λa b, associated.symm, λa b c, associated.trans⟩ }

end associated

local attribute [instance] associated.setoid

theorem unit_associated_one [monoid α] {u : units α} : (u : α) ~ᵤ 1 := ⟨u⁻¹, units.mul_inv u⟩

theorem associated_one_iff_is_unit [monoid α] {a : α} : (a : α) ~ᵤ 1 ↔ is_unit a :=
iff.intro
  (assume h, let ⟨c, h⟩ := h.symm in h ▸ ⟨c, one_mul _⟩)
  (assume ⟨c, h⟩, associated.symm ⟨c, by simp [h]⟩)

theorem associated_zero_iff_eq_zero [comm_semiring α] (a : α) : a ~ᵤ 0 ↔ a = 0 :=
iff.intro
  (assume h, let ⟨u, h⟩ := h.symm in by simpa using h.symm)
  (assume h, h ▸ associated.refl a)

theorem associated_one_of_mul_eq_one [comm_monoid α] {a : α} (b : α) (hab : a * b = 1) : a ~ᵤ 1 :=
show (units.mk_of_mul_eq_one a b hab : α) ~ᵤ 1, from unit_associated_one

theorem associated_one_of_associated_mul_one [comm_monoid α] {a b : α} :
  a * b ~ᵤ 1 → a ~ᵤ 1
| ⟨u, h⟩ := associated_one_of_mul_eq_one (b * u) $ by simpa [mul_assoc] using h

lemma associated_mul_mul [comm_monoid α] {a₁ a₂ b₁ b₂ : α} :
  a₁ ~ᵤ b₁ → a₂ ~ᵤ b₂ → (a₁ * a₂) ~ᵤ (b₁ * b₂)
| ⟨c₁, h₁⟩ ⟨c₂, h₂⟩ := ⟨c₁ * c₂, by simp [h₁.symm, h₂.symm, mul_assoc, mul_comm, mul_left_comm]⟩

theorem associated_of_dvd_dvd [integral_domain α] {a b : α} (hab : a ∣ b) (hba : b ∣ a) : a ~ᵤ b :=
begin
  haveI := classical.dec_eq α,
  rcases hab with ⟨c, rfl⟩,
  rcases hba with ⟨d, a_eq⟩,
  by_cases ha0 : a = 0,
  { simp [*] at * },
  have : a * 1 = a * (c * d),
  { simpa [mul_assoc] using a_eq },
  have : 1 = (c * d), from eq_of_mul_eq_mul_left ha0 this,
  exact ⟨units.mk_of_mul_eq_one c d (this.symm), by rw [units.mk_of_mul_eq_one, units.val_coe]⟩
end

def associates (α : Type*) [monoid α] : Type* :=
quotient (associated.setoid α)

namespace associates
open associated

protected def mk {α : Type*} [monoid α] (a : α) : associates α :=
⟦ a ⟧

theorem mk_eq_mk_iff_associated [monoid α] {a b : α} :
  associates.mk a = associates.mk b ↔ a ~ᵤ b :=
iff.intro quotient.exact quot.sound

theorem quotient_mk_eq_mk [monoid α] (a : α) : ⟦ a ⟧ = associates.mk a := rfl

theorem quot_mk_eq_mk [monoid α] (a : α) : quot.mk setoid.r a = associates.mk a := rfl

theorem forall_associated [monoid α] {p : associates α → Prop} :
  (∀a, p a) ↔ (∀a, p (associates.mk a)) :=
iff.intro
  (assume h a, h _)
  (assume h a, quotient.induction_on a h)

instance [monoid α] : has_one (associates α) := ⟨⟦ 1 ⟧⟩

theorem one_eq_mk_one [monoid α] : (1 : associates α) = associates.mk 1 := rfl

instance [monoid α] : has_bot (associates α) := ⟨1⟩

section comm_monoid
variable [comm_monoid α]

instance : has_mul (associates α) :=
⟨λa' b', quotient.lift_on₂ a' b' (λa b, ⟦ a * b ⟧) $
  assume a₁ a₂ b₁ b₂ ⟨c₁, h₁⟩ ⟨c₂, h₂⟩,
  quotient.sound $ ⟨c₁ * c₂, by simp [h₁.symm, h₂.symm, mul_assoc, mul_comm, mul_left_comm]⟩⟩

theorem mk_mul_mk {x y : α} : associates.mk x * associates.mk y = associates.mk (x * y) :=
rfl

instance : comm_monoid (associates α) :=
{ one       := 1,
  mul       := (*),
  mul_one   := assume a', quotient.induction_on a' $
    assume a, show ⟦a * 1⟧ = ⟦ a ⟧, by simp,
  one_mul   := assume a', quotient.induction_on a' $
    assume a, show ⟦1 * a⟧ = ⟦ a ⟧, by simp,
  mul_assoc := assume a' b' c', quotient.induction_on₃ a' b' c' $
    assume a b c, show ⟦a * b * c⟧ = ⟦a * (b * c)⟧, by rw [mul_assoc],
  mul_comm  := assume a' b', quotient.induction_on₂ a' b' $
    assume a b, show ⟦a * b⟧ = ⟦b * a⟧, by rw [mul_comm] }

instance : preorder (associates α) :=
{ le := λa b, ∃c, a * c = b,
  le_refl := assume a, ⟨1, by simp⟩,
  le_trans := assume a b c ⟨f₁, h₁⟩ ⟨f₂, h₂⟩, ⟨f₁ * f₂, h₂ ▸ h₁ ▸ (mul_assoc _ _ _).symm⟩}

instance [comm_monoid α] : has_dvd (associates α) := ⟨(≤)⟩

@[simp] lemma mk_one : associates.mk (1 : α) = 1 := rfl

lemma mk_pow (a : α) (n : ℕ) : associates.mk (a ^ n) = (associates.mk a) ^ n :=
by induction n; simp [*, pow_succ, associates.mk_mul_mk.symm]

lemma dvd_eq_le [comm_monoid α] : ((∣) : associates α → associates α → Prop) = (≤) := rfl

theorem prod_mk {p : multiset α} : (p.map associates.mk).prod = associates.mk p.prod :=
multiset.induction_on p (by simp; refl) $ assume a s ih, by simp [ih]; refl

theorem rel_associated_iff_map_eq_map {p q : multiset α} :
  multiset.rel associated p q ↔ p.map associates.mk = q.map associates.mk :=
by rw [← multiset.rel_eq];
  simp [multiset.rel_map_left, multiset.rel_map_right, mk_eq_mk_iff_associated]

theorem mul_eq_one_iff {x y : associates α} : x * y = 1 ↔ (x = 1 ∧ y = 1) :=
iff.intro
  (quotient.induction_on₂ x y $ assume a b h,
    have a * b ~ᵤ 1, from quotient.exact h,
    ⟨quotient.sound $ associated_one_of_associated_mul_one this,
      quotient.sound $ associated_one_of_associated_mul_one $ by rwa [mul_comm] at this⟩)
  (by simp {contextual := tt})

theorem prod_eq_one_iff {p : multiset (associates α)} :
  p.prod = 1 ↔ (∀a ∈ p, (a:associates α) = 1) :=
multiset.induction_on p
  (by simp)
  (by simp [mul_eq_one_iff, or_imp_distrib, forall_and_distrib] {contextual := tt})

theorem coe_unit_eq_one : ∀u:units (associates α), (u : associates α) = 1
| ⟨u, v, huv, hvu⟩ := by rw [mul_eq_one_iff] at huv; exact huv.1

theorem is_unit_iff_eq_one (a : associates α) : is_unit a ↔ a = 1 :=
iff.intro
  (assume ⟨u, h⟩, h.symm ▸ coe_unit_eq_one _)
  (assume h, h.symm ▸ is_unit_one)

theorem is_unit_mk {a : α} : is_unit (associates.mk a) ↔ is_unit a :=
calc is_unit (associates.mk a) ↔ a ~ᵤ 1 :
    by rw [is_unit_iff_eq_one, one_eq_mk_one, mk_eq_mk_iff_associated]
  ... ↔ is_unit a : associated_one_iff_is_unit

section order

theorem mul_mono {a b c d : associates α} (h₁ : a ≤ b) (h₂ : c ≤ d) :
  a * c ≤ b * d :=
let ⟨x, hx⟩ := h₁, ⟨y, hy⟩ := h₂ in
⟨x * y, by simp [hx.symm, hy.symm, mul_comm, mul_assoc, mul_left_comm]⟩

theorem one_le {a : associates α} : 1 ≤ a :=
⟨a, one_mul a⟩

theorem prod_le_prod {p q : multiset (associates α)} (h : p ≤ q) : p.prod ≤ q.prod :=
begin
  haveI := classical.dec_eq (associates α),
  haveI := classical.dec_eq α,
  suffices : p.prod ≤ (p + (q - p)).prod, { rwa [multiset.add_sub_of_le h] at this },
  suffices : p.prod * 1 ≤ p.prod * (q - p).prod, { simpa },
  exact mul_mono (le_refl p.prod) one_le
end

theorem le_mul_right {a b : associates α} : a ≤ a * b := ⟨b, rfl⟩

theorem le_mul_left {a b : associates α} : a ≤ b * a :=
by rw [mul_comm]; exact le_mul_right

end order

end comm_monoid

instance [has_zero α] [monoid α] : has_zero (associates α) := ⟨⟦ 0 ⟧⟩
instance [has_zero α] [monoid α] : has_top (associates α) := ⟨0⟩

section comm_semiring
variables [comm_semiring α]

@[simp] theorem mk_zero_eq (a : α) : associates.mk a = 0 ↔ a = 0 :=
⟨assume h, (associated_zero_iff_eq_zero a).1 $ quotient.exact h, assume h, h.symm ▸ rfl⟩

@[simp] theorem mul_zero : ∀(a : associates α), a * 0 = 0 :=
by rintros ⟨a⟩; show associates.mk (a * 0) = associates.mk 0; rw [mul_zero]

@[simp] theorem zero_mul : ∀(a : associates α), 0 * a = 0 :=
by rintros ⟨a⟩; show associates.mk (0 * a) = associates.mk 0; rw [zero_mul]

theorem mk_eq_zero_iff_eq_zero {a : α} : associates.mk a = 0 ↔ a = 0 :=
calc associates.mk a = 0 ↔ (a ~ᵤ 0) :  mk_eq_mk_iff_associated
  ... ↔ a = 0 : associated_zero_iff_eq_zero a

theorem dvd_of_mk_le_mk {a b : α} : associates.mk a ≤ associates.mk b → a ∣ b
| ⟨c', hc'⟩ := (quotient.induction_on c' $ assume c hc,
    let ⟨d, hd⟩ := (quotient.exact hc).symm in
    ⟨(↑d⁻¹) * c,
      calc b = (a * c) * ↑d⁻¹ : by rw [← hd, mul_assoc, units.mul_inv, mul_one]
        ... = a * (↑d⁻¹ * c) : by ac_refl⟩) hc'

theorem mk_le_mk_of_dvd {a b : α} : a ∣ b → associates.mk a ≤ associates.mk b :=
assume ⟨c, hc⟩, ⟨associates.mk c, by simp [hc]; refl⟩

theorem mk_le_mk_iff_dvd_iff {a b : α} : associates.mk a ≤ associates.mk b ↔ a ∣ b :=
iff.intro dvd_of_mk_le_mk mk_le_mk_of_dvd

def prime (p : associates α) : Prop := p ≠ 0 ∧ p ≠ 1 ∧ (∀a b, p ≤ a * b → p ≤ a ∨ p ≤ b)

lemma exists_mem_multiset_le_of_prime {s : multiset (associates α)} {p : associates α}
  (hp : prime p) :
  p ≤ s.prod → ∃a∈s, p ≤ a :=
multiset.induction_on s (assume ⟨d, eq⟩, (hp.2.1 (mul_eq_one_iff.1 eq).1).elim) $
assume a s ih h,
  have p ≤ a * s.prod, by simpa using h,
  match hp.2.2 a s.prod this with
  | or.inl h := ⟨a, multiset.mem_cons_self a s, h⟩
  | or.inr h := let ⟨a, has, h⟩ := ih h in ⟨a, multiset.mem_cons_of_mem has, h⟩
  end

lemma prime_mk (p : α) : prime (associates.mk p) ↔ _root_.prime p :=
begin
  rw [associates.prime, _root_.prime, forall_associated],
  transitivity,
  { apply and_congr, refl,
    apply and_congr, refl,
    apply forall_congr, assume a,
    exact forall_associated },
  apply and_congr,
  { rw [(≠), mk_zero_eq] },
  apply and_congr,
  { rw [(≠), ← is_unit_iff_eq_one, is_unit_mk], },
  apply forall_congr, assume a,
  apply forall_congr, assume b,
  rw [mk_mul_mk, mk_le_mk_iff_dvd_iff, mk_le_mk_iff_dvd_iff, mk_le_mk_iff_dvd_iff]
end

end comm_semiring

section integral_domain
variable [integral_domain α]

instance : partial_order (associates α) :=
{ le_antisymm := assume a' b',
    quotient.induction_on₂ a' b' $ assume a b ⟨f₁', h₁⟩ ⟨f₂', h₂⟩,
    (quotient.induction_on₂ f₁' f₂' $ assume f₁ f₂ h₁ h₂,
      let ⟨c₁, h₁⟩ := quotient.exact h₁, ⟨c₂, h₂⟩ := quotient.exact h₂ in
      quotient.sound $ associated_of_dvd_dvd
        (h₁ ▸ dvd_mul_of_dvd_left (dvd_mul_right _ _) _)
        (h₂ ▸ dvd_mul_of_dvd_left (dvd_mul_right _ _) _)) h₁ h₂
  .. associates.preorder }

instance : lattice.order_bot (associates α) :=
{ bot := 1,
  bot_le := assume a, one_le,
  .. associates.partial_order }

instance : lattice.order_top (associates α) :=
{ top := 0,
  le_top := assume a, ⟨0, mul_zero a⟩,
  .. associates.partial_order }

theorem zero_ne_one : (0 : associates α) ≠ 1 :=
assume h,
have (0 : α) ~ᵤ 1, from quotient.exact h,
have (0 : α) = 1, from ((associated_zero_iff_eq_zero 1).1 this.symm).symm,
zero_ne_one this

theorem mul_eq_zero_iff {x y : associates α} : x * y = 0 ↔ x = 0 ∨ y = 0 :=
iff.intro
  (quotient.induction_on₂ x y $ assume a b h,
    have a * b = 0, from (associated_zero_iff_eq_zero _).1 (quotient.exact h),
    have a = 0 ∨ b = 0, from mul_eq_zero_iff_eq_zero_or_eq_zero.1 this,
    this.imp (assume h, h.symm ▸ rfl) (assume h, h.symm ▸ rfl))
  (by simp [or_imp_distrib] {contextual := tt})

theorem prod_eq_zero_iff {s : multiset (associates α)} :
  s.prod = 0 ↔ (0 : associates α) ∈ s :=
multiset.induction_on s (by simp; exact zero_ne_one.symm) $
  assume a s, by simp [mul_eq_zero_iff, @eq_comm _ 0 a] {contextual := tt}

theorem irreducible_mk_iff (a : α) : irreducible (associates.mk a) ↔ irreducible a :=
begin
  simp [irreducible, is_unit_mk],
  apply and_congr (iff.refl _),
  split,
  { assume h x y eq,
    have : is_unit (associates.mk x) ∨ is_unit (associates.mk y),
      from h _ _ (by rw [eq]; refl),
    simpa [is_unit_mk] },
  { refine assume h x y, quotient.induction_on₂ x y (assume x y eq, _),
    rcases quotient.exact eq.symm with ⟨u, eq⟩,
    have : a = x * (y * u), by rwa [mul_assoc, eq_comm] at eq,
    show is_unit (associates.mk x) ∨ is_unit (associates.mk y),
    simpa [is_unit_mk] using h _ _ this }
end

lemma eq_of_mul_eq_mul_left [integral_domain α] :
  ∀(a b c : associates α), a ≠ 0 → a * b = a * c → b = c :=
begin
  rintros ⟨a⟩ ⟨b⟩ ⟨c⟩ ha h,
  rcases quotient.exact' h with ⟨u, hu⟩,
  have hu : a * (b * ↑u) = a * c, { rwa [← mul_assoc] },
  exact quotient.sound' ⟨u, eq_of_mul_eq_mul_left (mt (mk_zero_eq a).2 ha) hu⟩
end

lemma le_of_mul_le_mul_left [integral_domain α] (a b c : associates α) (ha : a ≠ 0) :
  a * b ≤ a * c → b ≤ c
| ⟨d, hd⟩ := ⟨d, eq_of_mul_eq_mul_left a _ _ ha $ by rwa ← mul_assoc⟩

lemma one_or_eq_of_le_of_prime [integral_domain α] :
  ∀(p m : associates α), prime p → m ≤ p → (m = 1 ∨ m = p)
| _ m ⟨hp0, hp1, h⟩ ⟨d, rfl⟩ :=
match h m d (le_refl _) with
| or.inl h := classical.by_cases (assume : m = 0, by simp [this]) $
  assume : m ≠ 0,
  have m * d ≤ m * 1, by simpa using h,
  have d ≤ 1, from associates.le_of_mul_le_mul_left m d 1 ‹m ≠ 0› this,
  have d = 1, from lattice.bot_unique this,
  by simp [this]
| or.inr h := classical.by_cases (assume : d = 0, by simp [this] at hp0; contradiction) $
  assume : d ≠ 0,
  have d * m ≤ d * 1, by simpa [mul_comm] using h,
  or.inl $ lattice.bot_unique $ associates.le_of_mul_le_mul_left d m 1 ‹d ≠ 0› this
end

end integral_domain

section normalization_domain
variable [normalization_domain α]

protected def out : associates α → α :=
begin
  refine quotient.lift (λa, a * ↑(norm_unit a)) _,
  letI := classical.dec_eq α,
  rintros a _ ⟨u, rfl⟩,
  by_cases a = 0, { simp [h] },
  calc a * ↑(norm_unit a) = a * ↑(u * norm_unit a * u⁻¹) :
      by rw [mul_comm u, mul_assoc, mul_inv_self, mul_one]
    ... = a * ↑u * ↑(norm_unit (a * ↑u)) :
      by simp [h, norm_unit_mul, units.coe_mul, units.coe_inv, mul_assoc]
end

lemma out_mk (a : α) : (associates.mk a).out = a * ↑(norm_unit a) :=
rfl

@[simp] lemma out_one : (1 : associates α).out = 1 :=
calc (1 : associates α).out = 1 * ↑(norm_unit (1 : α)) : out_mk _
  ... = 1 : by simp

lemma out_mul (a b : associates α) : (a * b).out = a.out * b.out :=
begin
  refine quotient.induction_on₂ a b (assume a b, _),
  simp [associates.quotient_mk_eq_mk, out_mk, mk_mul_mk],
  letI := classical.dec_eq α,
  by_cases a = 0; by_cases b = 0; simp [*, mul_assoc, mul_comm, mul_left_comm]
end

lemma dvd_out_iff (a : α) (b : associates α) : a ∣ b.out ↔ associates.mk a ≤ b :=
quotient.induction_on b $ by simp [associates.out_mk, associates.quotient_mk_eq_mk, mk_le_mk_iff_dvd_iff]

lemma out_dvd_iff (a : α) (b : associates α) : b.out ∣ a ↔ b ≤ associates.mk a :=
quotient.induction_on b $ by simp [associates.out_mk, associates.quotient_mk_eq_mk, mk_le_mk_iff_dvd_iff]

@[simp] lemma out_top : (⊤ : associates α).out = 0 :=
calc (⊤ : associates α).out = 0 * ↑(norm_unit (0:α)) : out_mk _
  ... = 0 : by simp

@[simp] lemma norm_unit_out (a : associates α) : norm_unit a.out = 1 :=
quotient.induction_on a $ assume a,
  by rw [associates.quotient_mk_eq_mk, associates.out_mk, norm_unit_mul_norm_unit]

end normalization_domain

end associates

def associates_int_equiv_nat : (associates ℤ) ≃ ℕ :=
begin
  refine ⟨λz, z.out.nat_abs, λn, associates.mk n, _, _⟩,
  { refine (assume a, quotient.induction_on a $ assume a,
      associates.mk_eq_mk_iff_associated.2 $ associated.symm $ ⟨norm_unit a, _⟩),
    simp [associates.out_mk, associates.quotient_mk_eq_mk, associated,
      int.coe_nat_abs_eq_mul_norm_unit.symm] },
  { assume n, simp [associates.out_mk, int.coe_nat_abs_eq_mul_norm_unit.symm] }
end
