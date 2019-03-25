import .reify .nnf

open expr tactic

meta def main : tactic unit :=
do dx ← get_domain, 
   ihx ← to_expr ``(inhabited),
   ix ← mk_instance (app ihx dx),
   rev dx,
   abst dx,
   reify dx ix,
   -- to_expr ``(form.rvalid_of_valid _) >>= apply,
   -- to_expr ``(@form.valid_of_closed_of_unsat_neg _ %%ix) >>= apply,
   -- exact_dec_trivial,
   skip

example (f g : nat → nat) : ∃ y : nat, (f y < y ∨ y ≤ g (y + 2)) := begin 
  main, 
  
  
  --apply form.rvalid_of_valid _,

end