import .rev .logic .tactic

open tactic expr

meta def arity_of : expr → nat 
| `(%%x → %%y) := arity_of y + 1
| _            := 0

meta def get_symb_aux (dx x : expr) : 
  tactic (expr × expr) :=
do tx ← infer_type x,
   if (is_pred_type dx tx || is_func_type dx tx)
   then return (x,tx)
   else failed

meta def get_symb (dx : expr) : 
  expr → tactic (expr × expr) 
| `(true)   := failed
| `(false)  := failed
| `(¬ %%px) := get_symb px
| `(%%px ∨ %%qx) := get_symb px <|> get_symb qx
| `(%%px ∧ %%qx) := get_symb px <|> get_symb qx
| (pi _ _ _ px) := get_symb px
| `(Exists %%(expr.lam _ _ _ px)) := get_symb px
| `(Exists %%prx) := get_symb prx 
| x@(app x1 x2) := 
       get_symb x1
  <|>  get_symb x2
  <|>  get_symb_aux dx x
| x := get_symb_aux dx x

meta def subst_symb (x : expr) : nat → expr → expr 
| k y@(app y1 y2) := 
  if x = y 
  then var k 
  else app (subst_symb k y1) (subst_symb k y2)
| k (lam n b tx y) := lam n b tx (subst_symb (k+1) y)
| k (pi n b tx y) := pi n b tx (subst_symb (k+1) y)
| k y := if x = y then var k else y

meta def abst_symb (dx : expr) : tactic unit := 
do gx ← target,
   (x,tx) ← get_symb dx gx,
   n ← get_unused_name,
   to_expr ``(imp_of_imp %%(pi n binder_info.default tx (subst_symb x 0 gx))) >>= apply,
   intro_fresh >>= apply,
   skip

meta def abst (dx : expr) : tactic unit := 
repeat (abst_symb dx)