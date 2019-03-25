import .form

variables {α : Type} 

namespace form


def skolem_term (k ms) : term := 
list.foldl (λ t1 m, t1 ^* # m) (& k) ms

def snf_core : nat → form → (nat × form)
| k ⊤*        := (k, ⊤*) 
| k ⊥*        := (k, ⊥*) 
| k (m ** ts) := (k, m ** ts)
| k (¬* p)    := (k, ¬* p)
| k (p ∧* q)  := 
  let (m, p') := snf_core k p in 
  let (n, q') := snf_core m q in 
  (n, p' ∧* q')
| k (p ∨* q)  := 
  let (m, p') := snf_core k p in 
  let (n, q') := snf_core m q in 
  (n, p' ∨* q')
| k (∀* p)    := 
  let (m, p') := snf_core k p in (m, ∀* p')
| k (∃* p)    := 
  let (m, p') := snf_core k p in 
  let xs := fv p' in
  (m+1, subst 0 (skolem_term m (fv p')) p')

def snf (p) := (snf_core (fresh_func_idx p) p).snd

#exit

lemma snf_equisat : ∀ p, (sat α (snf p) ↔ sat α p) := sorry


end form