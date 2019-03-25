
open expr tactic

meta def revert_cond (t : expr → tactic bool) (x : expr) : tactic unit :=
mcond (t x) (revert x >> skip) skip 

meta def revert_cond_all (t : expr → tactic bool) : tactic unit :=
do hs ← local_context, mmap (revert_cond t) hs, skip

meta def is_hyp (x : expr) : tactic bool :=
infer_type x >>= is_prop

meta def revert_hyps : tactic unit :=
revert_cond_all is_hyp >> skip

meta def has_type (tx x : expr) : tactic bool := 
do sx ← infer_type x, return (sx = tx)

meta def is_func_type (dx : expr) : expr → bool 
| `(%%x → %%y) := (x = dx) && (is_func_type y)
| x            := x = dx
meta def is_pred_type (dx : expr) : expr → bool 
| `(%%x → %%y) := (x = dx) && (is_pred_type y)
| x            := x = `(Prop)

meta def is_func (dx x : expr) : tactic bool :=
do y ← infer_type x, return $ is_func_type dx y

meta def is_pred (dx x : expr) : tactic bool :=
do y ← infer_type x,
   return $ is_pred_type dx y

-- Generalizes all free variables and hypotheses, 
-- and returns the expr of the domain.
meta def rev (dx : expr) : tactic unit :=
do revert_hyps,
   revert_cond_all (is_func dx),
   revert_cond_all (is_pred dx)