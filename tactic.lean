open expr tactic

meta def unifies_with_and (x : expr) : tactic (expr × expr) :=
do mv1 ← mk_meta_var `(Prop),
   mv2 ← mk_meta_var `(Prop),
   tactic.unify x `(%%mv1 ∧ %%mv2),
   return (mv1,mv2)

meta def split_ands_core : list expr → tactic unit 
| [] := skip 
| (x::xs) := 
  try (do 
    (px,qx) ← infer_type x >>= unifies_with_and,
    np ← get_unused_name, nq ← get_unused_name, 
    assertv np px (app (app (app `(@and.elim_left).to_expr px) qx) x),
    assertv nq qx (app (app (app `(@and.elim_right).to_expr px) qx) x)) >>
  split_ands_core xs

meta def split_ands : tactic unit := 
local_context >>= split_ands_core

meta def intro_fresh : tactic expr := 
do n ← get_unused_name, intro n