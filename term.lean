-- import .arity .list .logic
-- import .list 
import .simp_fol 

open tactic 

variables {α β : Type} 

structure model (α : Type) := 
(funcs : nat → list α → α)
(rels : nat → list α → Prop)

def func.default [inhabited α] (as : list α) : α := 
@inhabited.default _ _

def rel.default (as : list α) : Prop := false

def model.default [inhabited α] : model α := 
{ funcs := λ _, func.default,
  rels  := λ _, rel.default }

def cons (a : α) (f : nat → α) : nat → α
| 0     := a 
| (k+1) := f k

notation a `::` f := cons a f 

def model.cons_func (f : list α → α) (M : model α) : model α :=
{M with funcs := f::M.funcs, rels := rel.default::M.rels}

notation f `:f:` M := M.cons_func f 

def model.cons_rel [inhabited α] (r : list α → Prop) (M : model α) : model α :=
{M with funcs := func.default::M.funcs, rels := r::M.rels}

notation r `:r:` M := M.cons_rel r


@[derive has_reflect]
inductive term : Type 
| var : nat → term
| fnc : nat → term
| app : term → term → term

notation  `#` := term.var
notation  `&` := term.fnc
notation  t1 `^*` t2 := term.app t1 t2

-- | (# k) :=
-- | (& k) :=
-- | (t1 ^* t2) :=

namespace term

meta def to_string : term → string 
| (# k) := "#" ++ (to_fmt k).to_string
| (& k) := "&" ++ (to_fmt k).to_string
| (t1 ^* t2) := "(" ++ t1.to_string ++ " " ++ t2.to_string ++ ")"

meta instance has_repr : has_repr term := ⟨to_string⟩ 

@[fol] def max_idx_lt (k) : term → Prop 
| (# m)      := m < k
| (& _)      := true
| (t1 ^* t2) := t1.max_idx_lt ∧ t2.max_idx_lt

instance dec_max_idx_lt : ∀ k t, decidable (max_idx_lt k t) := 
begin
  intros k t, induction t; 
  simp_fol, repeat {apply_instance}, 
  apply @and.decidable _ _ _ _; assumption
end

@[fol] def val_core (M : model α) (v : nat → α) : term → list α → α 
| (# k)      _  := v k 
| (& k)      as := M.funcs k as
| (t1 ^* t2) as := t1.val_core (t2.val_core []::as)

@[fol] def val (M v t) : α := val_core M v t [] 

lemma val_core_eq_val_core_of_max_idx_lt :
  ∀ M (v w : nat → α) t as k, max_idx_lt k t → 
  (∀ m < k, v m = w m) → (val_core M v t as) = (val_core M w t as) 
| M v w (# k) as m h1 h2 := begin simp_fol, apply h2 _ h1 end 
| M v w (& k) as m h1 h2 := by simp_fol
| M v w (t1 ^* t2) as m h1 h2 :=
  begin
    simp_fol, cases h1,
    repeat {rw (val_core_eq_val_core_of_max_idx_lt M v w _ _ m)};
    assumption
  end

lemma val_eq_val_of_max_idx_lt (M) (v w : nat → α) (t k) : 
  max_idx_lt k t → (∀ m < k, v m = w m) → (val M v t) = (val M w t) :=
val_core_eq_val_core_of_max_idx_lt M v w t [] k 

def fv (k : nat) : term → list nat 
| (# m)      := if k ≤ m then [m] else []
| (& _)      := []
| (t1 ^* t2) := (fv t1) ∪ (fv t2)

def fresh_func_idx : term → nat 
| (# k)      := 0
| (& k)      := k + 1
| (t1 ^* t2) := max (fresh_func_idx t1) (fresh_func_idx t2)

def subst (m s) : term → term
| (# k)      := if k = m then s else (# k)
| (& k)      := (& k)
| (t1 ^* t2) := (subst t1) ^* (subst t2)

def incr_vdx : term → term
| (# k)      := # (k+1)
| (& k)      := (& k)
| (t1 ^* t2) := t1.incr_vdx ^* t2.incr_vdx

end term