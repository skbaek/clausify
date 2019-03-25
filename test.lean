import tactic.basic

open tactic

local attribute [instance] classical.prop_decidable

example : true ↔ ¬false :=
by exact_dec_trivial

#exit

def foo (n : nat) : Prop := n = 0

instance : decidable_pred foo :=
begin intro n, simp [foo], apply_instance end

instance baz {α} {p : α → Prop} [decidable_pred p] 
  (l : list α) : decidable (∀ x ∈ l, p x) :=
begin
  cases l, apply decidable.is_true, intros x h, cases h,
  rw list.forall_mem_cons, apply and.decidable,
end


example {α} {p : α → Prop} {a : α} {l : list α} :
  (∀ (x : α), x = a ∨ x ∈ l → p x) ↔ p a ∧ ∀ x ∈ l, p x :=
begin 
  simp only [or_imp_distrib], 
  simp only [forall_and_distrib],
  simp only [forall_eq],

end

#check @propext
#check @list.forall_mem_cons'
#check @or_imp_distrib
#check @forall_and_distrib
#check @forall_eq
#print axioms list.forall_mem_cons'
#print axioms or_imp_distrib
#print axioms forall_and_distrib
#print axioms forall_eq

#exit
example : ∀ n ∈ [0], foo n :=
by tactic.exact_dec_trivial

#exit

instance bar {α} {p : α → Prop} [decidable_pred p] 
  (l : list α) : decidable (∀ x ∈ l, p x) :=
decidable_of_iff _ list.all_iff_forall_prop
-- 


#exit

def quux (n : nat) : nat := 
begin
  apply n
end

example : 0 = quux 0 := rfl

#exit
import tactic.basic

run_cmd mk_simp_attr `fol

meta def simp_fol := `[simp only with fol]

@[derive has_reflect]
inductive term : Type 
| var : nat → term
| fnc : nat → term
| app : term → term → term

notation  `#` := term.var
notation  `&` := term.fnc
notation  t1 `^*` t2 := term.app t1 t2

@[derive has_reflect]
inductive form : Type 
| false : form
| true : form
| prd : nat → list term → form 
| not : form → form
| or  : form → form → form
| and : form → form → form
| fa  : form → form
| ex  : form → form

notation  `⊤*` := form.true
notation  `⊥*` := form.false
notation  p `**` ts := form.prd p ts
notation  `¬*` := form.not
notation  p `∧*` q := form.and p q
notation  p `∨*` q := form.or p q
notation  `∀*` := form.fa
notation  `∃*` := form.ex 

@[fol] def term.max_idx_lt (k) : term → Prop 
| (# m)      := m < k
| (& _)      := true
| (t1 ^* t2) := t1.max_idx_lt ∧ t2.max_idx_lt

instance dec_max_idx_lt : ∀ k t, decidable (term.max_idx_lt k t) := 
begin
  intros k t, induction t; 
  simp_fol, repeat {apply_instance}, 
  apply @and.decidable _ _ _ _; assumption
end

@[fol] def form.max_idx_lt : nat → form → Prop 
| k ⊥*        := _root_.true
| k ⊤*        := _root_.true
| k (m ** ts) := ∀ t ∈ ts, term.max_idx_lt k t
| k (¬* p)    := p.max_idx_lt k
| k (p ∨* q)  := p.max_idx_lt k ∧ q.max_idx_lt k
| k (p ∧* q)  := p.max_idx_lt k ∧ q.max_idx_lt k
| k (∀* p)    := p.max_idx_lt (k+1)
| k (∃* p)    := p.max_idx_lt (k+1)

@[fol] def closed (p : form) : Prop := p.max_idx_lt 0

open tactic

meta def induce (t : tactic unit := skip) : tactic unit := 
`[ intro p, induction p with k ts p ih p q ihp ihq p q ihp ihq p ih p ih; t ]

instance form.dec_max_idx_lt : ∀ p : form, ∀ k, decidable (p.max_idx_lt k) :=
begin
  induce `[intro k, try {simp_fol}, try {apply_instance},
    try {apply @and.decidable _ _ _ _}, try {apply ih},
    try {apply ihp}, try {apply ihq}], 
end

instance dec_closed (p : form) : decidable (closed p) := p.dec_max_idx_lt 0

example : closed (∃* (1 **[# 0])) :=
begin
  exact_dec_trivial
end