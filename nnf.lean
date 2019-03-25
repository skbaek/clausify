import .form

variables {α : Type} 

namespace form

@[fol] def push_neg : form → form
| ⊤*        := ⊥*  
| ⊥*        := ⊤* 
| (k ** ts) := ¬* (k ** ts)
| (p ∨* q)  := push_neg p ∧* push_neg q
| (p ∧* q)  := push_neg p ∨* push_neg q
| (∀* p)    := ∃* (push_neg p)
| (∃* p)    := ∀* (push_neg p)
| (¬* p)    := p

@[fol] def nnf : form → form
| ⊤*        := ⊤*  
| ⊥*        := ⊥* 
| (k ** ts) := (k ** ts)
| (¬* p)    := push_neg (nnf p)
| (p ∨* q) := (nnf p) ∨* (nnf q)
| (p ∧* q) := (nnf p) ∧* (nnf q)
| (∀* p) := ∀* (nnf p)
| (∃* p) := ∃* (nnf p)

open tactic

local attribute [instance] classical.prop_decidable

lemma push_neg_equiv : ∀ p, equiv α (push_neg p) (¬* p) :=
begin
  induce `[intros M v, try {simp_fol}], simp, simp, simp,
  { rw not_or_distrib, apply and_iff_and, apply ihp, apply ihq },
  { rw not_and_distrib, apply or_iff_or, apply ihp, apply ihq },
  { rw not_forall, apply exists_iff_exists, intro x, apply ih },
  { rw not_exists, apply forall_iff_forall, intro x, apply ih }
end

lemma nnf_equiv : ∀ p, equiv α (nnf p) p :=
begin
  induce `[intros M v, try {simp_fol}, try {trivial}], 
  { apply iff.trans, apply push_neg_equiv,
    apply not_iff_not_of_iff, apply ih },
  { apply or_iff_or, apply ihp, apply ihq },
  { apply and_iff_and, apply ihp, apply ihq },
  { apply forall_iff_forall, intro x, apply ih },
  { apply exists_iff_exists, intro x, apply ih }
end

end form