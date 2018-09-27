/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Sean Leather

List folds generalized to `traversable`.
-/
import tactic.squeeze
import algebra.group
import data.list.basic
import category.traversable.instances category.traversable.lemmas
import category_theory.category category_theory.types category_theory.opposites category_theory.instances.kleisli
import category.applicative

universes u v

open ulift category_theory

namespace monoid

@[reducible] def foldl (α : Type u) : Type u := End α
def foldl.mk {α} (f : α → α) : foldl α := f

@[reducible] def foldr (α : Type u) : Type u := (End α)ᵒᵖ
def foldr.mk {α : Type u} (f : α → α) : foldr α := f

@[reducible] def mfoldl (m : Type u → Type u) [monad m] (α : Type u) : Type u := End $ Kleisli.mk m α
def mfoldl.mk {m} [monad m] {α} (f : α → m α) : mfoldl m α := f

@[reducible] def mfoldr (m : Type u → Type u) [monad m] (α : Type u) : Type u := (End $ Kleisli.mk m α)ᵒᵖ
def mfoldr.mk {m} [monad m] {α} (f : α → m α) : mfoldr m α := f

end monoid

namespace traversable
open monoid functor

section defs
variables {α β : Type u} {t : Type u → Type u} [traversable t]

def fold_map {α ω} [has_one ω] [has_mul ω] (f : α → ω) : t α → ω :=
traverse (const.mk' ∘ f)

def foldl (f : α → β → α) (x : α) (xs : t β) : α :=
fold_map (foldl.mk ∘ flip f) xs x

def foldr (f : α → β → β) (x : β) (xs : t α) : β :=
fold_map (foldr.mk ∘ f) xs x

/--
`to_list_spec` provides an alternative definition for `to_list`:
`fold_map list.ret`

The definition based on `foldr` is faster than using `list` as a
monoid. Each insertion is done in constant time. In sum, `to_list`
performs in linear. On the other hand, `fold_map list.ret` creates a
singleton list around each element and concatenates all the resulting
lists. In `xs ++ ys`, concatenation takes a time proportional to
`length xs`. Since the order in which concatenation is evaluated is
unspecified, nothing prevents each element of the traversable to be
appended at the end `xs ++ [x]` which yields `O(n²)` run time. -/
def to_list : t α → list α :=
list.reverse ∘ foldl (flip list.cons) []

def length (xs : t α) : ℕ :=
down $ foldl (λ l _, up $ l.down + 1) (up 0) xs

variables {m : Type u → Type u} [monad m]

def mfoldl (f : α → β → m α) (x : α) (xs : t β) : m α :=
fold_map (mfoldl.mk ∘ flip f) xs x

def mfoldr (f : α → β → m β) (x : β) (xs : t α) : m β :=
fold_map (mfoldr.mk ∘ f) xs x

end defs

section applicative_transformation
variables {α β γ : Type u}

open function (hiding const) is_monoid_hom

def map_fold [monoid α] [monoid β] (f : α → β) [is_monoid_hom f] :
  applicative_transformation (const α) (const β) :=
{ app := λ x, f,
  preserves_seq'  := by { intros, simp only [map_mul f], },
  preserves_pure' := by { intros, simp only [map_one f] } }

def free.mk : α → free_monoid α := list.ret

def free.map (f : α → β) : free_monoid α → free_monoid β := list.map f

lemma free.map_eq_map (f : α → β) (xs : list α) :
  f <$> xs = free.map f xs := rfl

instance (f : α → β) : is_monoid_hom (free.map f) :=
by constructor; simp [free.map]

instance fold_foldl (f : β → α → β) :
  @is_monoid_hom (free_monoid α) (monoid.foldl β) _ _ (flip $ list.foldl f) :=
{ map_one := rfl,
  map_mul := by { intros, unfold_projs, simp [flip] } }

instance fold_foldr (f : α → β → β) :
  @is_monoid_hom (free_monoid α) (monoid.foldr β) _ _ (flip $ list.foldr f) :=
{ map_one := rfl,
  map_mul := by { intros, simp [flip], unfold_projs, simp } }

variables (m : Type u → Type u) [monad m] [is_lawful_monad m]

instance fold_mfoldl (f : β → α → m β) :
  @is_monoid_hom (free_monoid α) (monoid.mfoldl m β) _ _ (flip $ list.mfoldl f) :=
{ map_one := rfl,
  map_mul := by { intros, unfold_projs, simp [flip] } }

instance fold_mfoldr (f : α → β → m β) :
  @is_monoid_hom (free_monoid α) (monoid.mfoldr m β) _ _ (flip $ list.mfoldr f) :=
{ map_one := rfl,
  map_mul := by { intros, simp [flip], unfold_projs, simp } }

variables {t : Type u → Type u} [traversable t] [is_lawful_traversable t]
open is_lawful_traversable

lemma fold_map_hom (α β)
  [monoid α] [monoid β] (f : α → β) [is_monoid_hom f]
  (g : γ → α) (x : t γ) :
  f (fold_map g x) = fold_map (f ∘ g) x :=
calc  f (fold_map g x)
    = f (traverse (const.mk' ∘ g) x)  : rfl
... = (map_fold f).app _ (traverse (const.mk' ∘ g) x) : rfl
... = traverse ((map_fold f).app _ ∘ (const.mk' ∘ g)) x : naturality (map_fold f) _ _
... = fold_map (f ∘ g) x : rfl

variable {m}

lemma fold_mfoldl_cons (f : α → β → m α) (x : β) (y : α) :
  list.mfoldl f y (list.ret x) = f y x :=
by simp [list.ret, list.mfoldl, flip]

lemma fold_mfoldr_cons (f : β → α → m α) (x : β) (y : α) :
  list.mfoldr f y (list.ret x) = f x y :=
by simp [list.ret, list.mfoldr, flip]

end applicative_transformation

section equalities
open is_lawful_traversable list (cons)
variables {α β γ : Type u}
variables {t : Type u → Type u} [traversable t] [is_lawful_traversable t]

lemma to_list_spec (xs : t α) :
  to_list xs = (fold_map free.mk xs : free_monoid _) :=
eq.symm $
calc  fold_map free.mk xs
    = (fold_map free.mk xs).reverse.reverse : by simp only [list.reverse_reverse]
... = (list.foldr cons [] (fold_map free.mk xs).reverse).reverse
                 : by simp only [list.foldr_eta]
... = (flip (list.foldl (flip cons)) (fold_map free.mk xs : free_monoid α) []).reverse
                 : by simp only [flip,list.foldr_reverse]
... = to_list xs : by simp [fold_map_hom (free_monoid α) (monoid.foldl _) (flip (list.foldl $ flip cons)) _]; refl

lemma fold_map_map [monoid γ]  (f : α → β) (g : β → γ) (xs : t α) :
  fold_map g (f <$> xs) = fold_map (g ∘ f) xs :=
by simp only [fold_map,traverse_map]

lemma foldl_to_list (f : α → β → α) (xs : t β) (x : α) :
  foldl f x xs = list.foldl f x (to_list xs) :=
by { change _ = flip (list.foldl f) _ _,
     simp [foldl, to_list_spec, fold_map_hom (free_monoid β) (monoid.foldl α) (flip (list.foldl f))],
     refl }

lemma foldr_to_list (f : α → β → β) (xs : t α) (x : β) :
  foldr f x xs = list.foldr f x (to_list xs) :=
by { change _ = flip (list.foldr f) _ _,
     simp [foldr, to_list_spec, fold_map_hom (free_monoid α) (monoid.foldr β) (flip (list.foldr f))],
     refl }

lemma to_list_map (f : α → β) (xs : t α) :
  to_list (f <$> xs) = f <$> to_list xs :=
by simp only [to_list_spec,free.map_eq_map,fold_map_hom _ _ (free.map f), fold_map_map]; refl

@[simp] theorem foldl_map (g : β → γ) (f : α → γ → α) (a : α) (l : t β) :
  foldl f a (g <$> l) = foldl (λ x y, f x (g y)) a l :=
by simp only [foldl, fold_map_map, (∘), flip]

@[simp] theorem foldr_map (g : β → γ) (f : γ → α → α) (a : α) (l : t β) :
  foldr f a (g <$> l) = foldr (f ∘ g) a l :=
by simp only [foldr, fold_map_map, (∘), flip]

@[simp] theorem to_list_eq_self {xs : list α} : to_list xs = xs :=
begin
  simp only [to_list_spec, fold_map, traverse],
  induction xs,
  case list.nil { refl },
  case list.cons : _ _ ih { unfold list.traverse list.ret, rw ih, refl }
end

theorem length_to_list {xs : t α} : length xs = list.length (to_list xs) :=
begin
  unfold length,
  rw foldl_to_list,
  generalize : to_list xs = ys,
  let f := λ (n : ℕ) (a : α), n + 1,
  transitivity list.foldl f 0 ys,
  { generalize : 0 = n,
    induction ys with _ _ ih generalizing n,
    { simp },
    { simp only [list.foldl, ih (n+1)] } },
  { induction ys with _ tl ih,
    { simp },
    { simp only [list.foldl, list.length],
      transitivity list.foldl f 0 tl + 1,
      { exact eq.symm (list.foldl_hom (+1) f f 0 (λ _ _, rfl) _) },
      { rw ih } } }
end

variables {m : Type u → Type u} [monad m] [is_lawful_monad m]

lemma mfoldl_to_list {f : α → β → m α} {x : α} {xs : t β} :
  mfoldl f x xs = list.mfoldl f x (to_list xs) :=
by { change _ = flip (list.mfoldl f) _ _,
     simp only [mfoldl, to_list_spec, fold_map_hom (free_monoid β) (monoid.mfoldl m α) (flip (list.mfoldl f))],
     simp only [flip, (∘), fold_mfoldl_cons, free.mk], refl }

lemma mfoldr_to_list (f : α → β → m β) (x : β) (xs : t α) :
  mfoldr f x xs = list.mfoldr f x (to_list xs) :=
by { change _ = flip (list.mfoldr f) _ _,
     simp only [mfoldr, to_list_spec, fold_map_hom (free_monoid α) (monoid.mfoldr m β) (flip (list.mfoldr f))],
     simp only [flip, (∘), fold_mfoldr_cons, free.mk], refl }

@[simp] theorem mfoldl_map (g : β → γ) (f : α → γ → m α) (a : α) (l : t β) :
  mfoldl f a (g <$> l) = mfoldl (λ x y, f x (g y)) a l :=
by simp only [mfoldl, fold_map_map, (∘), flip]

@[simp] theorem mfoldr_map (g : β → γ) (f : γ → α → m α) (a : α) (l : t β) :
  mfoldr f a (g <$> l) = mfoldr (f ∘ g) a l :=
by simp only [mfoldr, fold_map_map, (∘), flip]

end equalities

end traversable
