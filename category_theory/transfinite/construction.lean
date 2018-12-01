import category_theory.transfinite.misc

noncomputable theory

local attribute [instance] classical.dec

open category_theory category_theory.functor

universes u v

namespace category_theory.transfinite

section

parameters {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

section build
/- Note on building transfinite compositions

Suppose our aim is to construct a transfinite composition of some
particular "length" γ, γ being a well-ordered type with a greatest
element. This consists of a collection of objects X i for i : γ and
morphisms X i → X j for i j : γ, i ≤ j satisfying some conditions. We
want to construct these by transfinite recursion, forming a colimit at
limit stages and applying some other construction at successor stages.

This is tricky to do by a direct recursion because the objects and
morphisms depend on each other. Obviously the map we append at stage
i+1 must depend on the object X i, but at limit stages we need to form
the next object as a colimit and this construction depends on all the
previous maps. Moreover, in order to continue the construction and
form this colimit, we need to use the fact that the maps chosen so far
actually do define a functor.

In order to organize this construction, we apply the principle of
"consistent recursion". Namely, we will construct for each i : γ a
transfinite composition on the closed initial segment [⊥, i] of γ,
while requiring that for each i < j, the transfinite composition on
[⊥, i] is (strictly!) equal to the restriction of the transfinite
composition on [⊥, j]. (This condition relies on the ability to talk
about the *set* of objects of a category. If we wanted to use only
equivalence-invariant concepts, we'd need to instead construct
isomorphisms here which in turn satisfy some coherence conditions.)
At the end of the process, we have a transfinite composition on [⊥, ⊤]
which we transfer to the original type γ.

This section contains the building blocks for such a construction. For
each type of i (base case, successor case and limit case), we provide
a constructor for building a transfinite composition on [⊥, i] from
consistent transfinite compositions on the earlier segments, and a
lemma showing that the new transfinite composition is consistent with
the previous ones. We also provide a "finalizing" constructor which
transfers a transfinite composition on [⊥, ⊤] to γ.

(TODO: Probably want something more general for this last step, namely
restricting a transfinite composition along the inclusion of an
initial segment (ordinal.initial_seg). Then apply to γ → [⊥, ⊤].)

-/

parameters {I : morphism_class C}

parameters {γ : Type v} [lattice.order_top γ] [is_well_order γ (<)]


-- parameters [limits.has_colimits C]

#exit

section induction
-- Now, having done all the hard work just once (hopefully?), we
-- provide specialized methods to extend at each type of stage:
-- bot, succ, limit.

section bot
-- To start, the required data is just an object X.
parameters (X : C)

/-- A transfinite composition of "length zero". It consists of a
  single object, X. The conditions on successor and limit steps are
  vacuously satisfied. -/
def build_tcomp_bot : transfinite_composition I (below_top (bot : γ)) :=
{ F := (const _).obj X,
  succ := begin
    intros i j h,
    refine absurd (lt_of_lt_of_le h.lt _) (not_lt_bot _),
    change j.val ≤ _,
    convert j.property,
    rw ←is_bot_iff
  end,
  limit := begin
    intros j h,
    refine absurd j.property (not_le_of_lt _),
    convert h.bot_lt,
    symmetry,
    rw ←is_bot_iff
  end }

/-- The base case is vacuously consistent with previous stages,
  because there are none. TODO: Determine what form is most convenient
  at the use site -/
lemma build_tcomp_bot_consistent : true := trivial

end bot

-- In the remaining two cases (succ and build),
-- * k is the stage we're constructing
-- * Z encodes the choices of all the earlier segments
-- * hZ is the condition that these were compatible

parameters {k : γ} (Z : Π (i < k), transfinite_composition I (below_top i))
parameters (hZ : ∀ i i' (hik : i < k) (hi'k : i' < k) (hii' : i < i'),
  embed (le_of_lt hii') ⋙ (Z i' hi'k).F = (Z i hik).F)

-- We can include the case i = i' for free
lemma hZ' : ∀ i i' (hik : i < k) (hi'k : i' < k) (hii' : i ≤ i'),
  embed hii' ⋙ (Z i' hi'k).F = (Z i hik).F :=
sorry

section succ
-- The successor case: Suppose k is the successor of another element j.
parameters {j : γ} (hjk : is_succ j k)

-- To extend the construction, we should give a morphism from the end
-- of the previous stage which belongs to I.
parameters {Y : C} (f : (Z j hjk.lt).F.obj ⊤ ⟶ Y) (hf : I f)

-- TODO: is this the best way to make a short name for ⟨p.1, hjk.le_of_lt_succ hp⟩

-- TODO: This below is unused
@[reducible] private def restriction {p : below_top k} (hp : p.1 < k) : below_top j :=
⟨p.1, hjk.le_of_lt_succ hp⟩

local notation `restr` hp:1000 := (⟨subtype.val _, hjk.le_of_lt_succ hp⟩ : below_top _)

include hf

-- First build the new underlying functor
def build_tcomp_succ_F : below_top k ⥤ C :=
  { obj := λ p, if hp : p.val < k then (Z j hjk.lt).F.obj (restr hp) else Y,
    map := λ p p' hpp',
      if hp' : p'.val < k then
        have hp : p.val < k, from lt_of_le_of_lt hpp'.down.down hp',
        change_hom ((Z j hjk.lt).F.obj (restr hp)) ((Z j hjk.lt).F.obj (restr hp'))
          (by simp [hp]) (by simp [hp'])
        ((Z j hjk.lt).F.map hpp')
      else if hp : p.val < k then
        change_hom ((Z j hjk.lt).F.obj (restr hp)) Y
          (by simp [hp]) (by simp [hp'])
        ((Z j hjk.lt).F.map ⟨⟨lattice.le_top⟩⟩ ≫ f)
      else
        change_hom Y Y (by simp [hp]) (by simp [hp']) (𝟙 Y),
    map_id' := λ p, begin
      split_ifs;
      { dsimp [change_hom],
        try { erw (Z j _).F.map_id },
        simp }
    end,
    map_comp' := λ p p' p'' hpp' hp'p'', begin
      by_cases hp'' : p''.val < k,
      { have hp' : p'.val < k, from lt_of_le_of_lt hp'p''.down.down hp'',
        have hp : p.val < k, from lt_of_le_of_lt hpp'.down.down hp',
        simp [hp, hp', hp''],
        erw (Z j hjk.lt).F.map_comp  
          (show restr hp ⟶ restr hp', from hpp')
          (show restr hp' ⟶ restr hp'', from hp'p''),
        simp },
      by_cases hp' : p'.val < k,
      { have hp : p.val < k, from lt_of_le_of_lt hpp'.down.down hp',
        simp [hp, hp', hp''],
        erw (Z j hjk.lt).F.map_comp  
          (show restr hp ⟶ restr hp', from hpp')
          ⟨⟨lattice.le_top⟩⟩,
        simp },
      by_cases hp : p.val < k; { simp [hp, hp', hp'', change_hom] }
    end }

lemma build_tcomp_succ_F_extends_j : embed hjk.le ⋙ build_tcomp_succ_F = (Z j hjk.lt).F :=
begin
  dunfold build_tcomp_succ_F,
  fapply category_theory.functor.ext,
  { intro p,
    have hp : ((embed hjk.le).obj p).val < k, from lt_of_le_of_lt p.property hjk.lt,
    simp [hp],
    cases p, refl },
  { intros p p' hpp',
    have hp : ((embed hjk.le).obj p).val < k, from lt_of_le_of_lt p.property hjk.lt,
    have hp' : ((embed hjk.le).obj p').val < k, from lt_of_le_of_lt p'.property hjk.lt,
    dsimp, simp [hp, hp'],
    cases p, cases p', congr }
end

/-- A transfinite composition formed by extending the previous one by
  a single morphism, f. -/
def build_tcomp_succ : transfinite_composition I (below_top k) :=
{ F := build_tcomp_succ_F,
  succ := λ p p' spp', begin
    dunfold build_tcomp_succ_F,
    have hp : p.val < k, from lt_of_lt_of_le spp'.lt p'.property,
    by_cases hp' : p'.val < k,
    { simp [hp, hp', -change_hom, I_change_hom I],
      refine (Z j hjk.lt).succ (restr hp) (restr hp') _,
      -- Need to know that is_succ (restr hp) (restr hp'), still.
      sorry },
    { simp [hp, hp', -change_hom, I_change_hom I],
      have : p.val = j, from sorry,
      -- ^ p'.val is k, and we have is_succ j k and is_succ p p'.
      subst this,
      convert hf,
      convert category.id_comp _ _,
      apply (Z _ _).F.map_id }
  end,
  limit := λ p hp, begin
    have hp : p.val < k, from sorry, -- it's a limit ordinal, not successor
    have : p = (below_initial_seg hjk.le) (restr hp), by cases p; refl,
    rw this,
    rw smooth_at_iff_restriction_smooth_at (below_initial_seg hjk.le),
    dsimp [restriction],
    erw build_tcomp_succ_F_extends_j,
    apply (Z j _).limit,
    sorry -- it's still a limit ordinal
  end }

lemma build_tcomp_succ_extends (i) (hik : i < k) :
  embed (le_of_lt hik) ⋙ build_tcomp_succ.F = (Z i hik).F :=
have bt : _ := build_tcomp_succ_F_extends_j,
have _ := hZ' i j hik hjk.lt (hjk.le_of_lt_succ hik),
by rw [←this, ←bt]; refl

end succ

section limit
-- The limit case: k is a limit step.
parameters (hk : is_limit k)

-- Maybe we could have made this more uniform? Always ask for a new
-- object plus compatible maps from the ends of each previous
-- composition.

include hZ
def build_tcomp_limit_diagram : {i // i < k} ⥤ C :=
{ obj := λ p, (Z p.val p.property).F.obj ⊤,
  map := λ p p' hpp',
    eq_to_hom (eq_obj (hZ' p.val p'.val p.property p'.property hpp'.down.down).symm _) ≫
    (Z p'.val p'.property).F.map hpp',
  map_id' := λ p, by erw (Z _ _).F.map_id; simp; refl,
  map_comp' := λ p p' p'' hpp' hp'p'', let hZ' := hZ' in begin
    rw eq_hom (hZ' p'.val p''.val p'.property p''.property hp'p''.down.down).symm
      (show (⟨p.val, hpp'.down.down⟩ : below_top p'.val) ⟶ (⟨p'.val, le_refl _⟩ : below_top p'.val),
       from hpp'),
    dsimp,
    simp,
    congr,
    apply (Z p''.val p''.property).F.map_comp,
  end }

/-
def build_tcomp_limit_F : below_top k ⥤ C :=
{ obj := λ p,
    if hp : p.val < k then (Z p.val hp).F.obj ⊤ else
    limits.colimit _ }
-/

end limit

end induction

end build

#exit

variables (F : C ⥤ C) (α : functor.id C ⟹ F)

variables (γ : Type v) [lattice.order_top γ] [is_well_order γ (<)]

#check transfinite_composition

-- no! use an inductive Prop
def strict_image : morphism_class C :=
λ X Y f, Y = F.obj X ∧ f == α.app X

noncomputable def build_transfinite_composition (X : C) :
  Σ' (c : transfinite_composition (strict_image F α) γ), c.F.obj bot = X :=
begin
  suffices : Π (i : γ), Σ' (c : transfinite_composition (strict_image F α) (below_top i)),
    c.F.obj bot = X,
  { have c' := this ⊤,
    refine ⟨⟨to_below_top.comp c'.fst.F, _, _⟩, _⟩,
    { intros i j h, apply c'.fst.succ, rwa is_succ_iff },
    { intros j h,
      have := c'.fst.limit (to_below_top.obj j) (by rwa is_limit_iff),
      dsimp [smooth_at] at ⊢ this,
      -- This is a mess--we need to show that the transported diagram is still a colimit
      sorry },
    { convert c'.snd using 1,
      change c'.fst.F.obj _ = _,
      congr,
      rw is_bot_iff,
      refl } },

  refine crec (is_well_order.wf (<))
    (λ i i hii' p p', embed (le_of_lt hii') ⋙ p'.1.F = p.1.F) _,
  rintros j ⟨Z, hZ⟩,

  rcases is_bot_or_succ_or_limit j with ⟨_,rfl⟩|⟨i,_,hij⟩|⟨_,hj⟩,

  { refine ⟨⟨⟨(category_theory.functor.const _).obj X, _, _⟩, _⟩, _⟩,
    { intros i j h,
      refine absurd (lt_of_lt_of_le h.lt _) (not_lt_bot _),
      change j.val ≤ _,
      convert j.property,
      rw ←is_bot_iff },
    { intros j h,
      refine absurd j.property (not_le_of_lt _),
      convert h.bot_lt,
      symmetry,
      rw ←is_bot_iff },
    { refl },
    { exact λ j h, absurd h (not_lt_bot _) } },

  { refine ⟨⟨⟨_, _, _⟩, _⟩, _⟩,
    -- Should do some preliminary constructions first.
    -- Extending a functor from `below_top j` to `below_top j'` where `is_succ j j'`, etc.
},
end

end
end category_theory.transfinite
