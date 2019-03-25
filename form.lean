import .term  tactic.basic .list .arity .tactic .logic .nat

open tactic

variables {α β : Type} 

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

-- | ⊤*        := sorry
-- | ⊥*        := sorry
-- | (k ** ts) := sorry
-- | (¬* p)    := sorry
-- | (p ∧* q)  := sorry
-- | (p ∨* q)  := sorry
-- | (∀* p)  := sorry
-- | (∃* p)  := sorry

namespace form

meta def to_string : form → string 
| ⊥* := "⊥"
| ⊤* := "⊤"
| (k ** ts) := "(" ++ (to_fmt k).to_string ++ (ts.map term.to_string).to_string ++ ")" 
| (¬* φ)    := "¬" ++ φ.to_string
| (φ ∨* ψ) := "(" ++ (φ.to_string) ++ " ∨ " ++ (ψ.to_string) ++ ")"
| (φ ∧* ψ) := "(" ++ (φ.to_string) ++ " ∧ " ++ (ψ.to_string) ++ ")"
| (∀* φ) := "∀" ++ φ.to_string
| (∃* φ) := "∃" ++ φ.to_string

meta instance has_to_string : has_to_string form := ⟨form.to_string⟩
meta instance has_repr : has_to_string form := ⟨form.to_string⟩
meta instance has_to_format : has_to_format form := ⟨λ f, to_string f⟩

meta def induce (t : tactic unit := skip) : tactic unit := 
`[ intro p, induction p with k ts p ih p q ihp ihq p q ihp ihq p ih p ih; t ]

meta def induce_iff (t : tactic unit := skip) : tactic unit := 
induce t >> 
focus [ skip, skip, skip, 
  `[ apply not_iff_not_of_iff ],
  `[ apply or_iff_or   ],
  `[ apply and_iff_and ],
  `[ apply forall_iff_forall, intro ],
  `[ apply exists_iff_exists, intro ] ] 
   
@[fol] def max_idx_lt : nat → form → Prop 
| k ⊥*        := _root_.true
| k ⊤*        := _root_.true
| k (m ** ts) := ∀ t ∈ ts, term.max_idx_lt k t
| k (¬* p)    := p.max_idx_lt k
| k (p ∨* q)  := p.max_idx_lt k ∧ q.max_idx_lt k
| k (p ∧* q)  := p.max_idx_lt k ∧ q.max_idx_lt k
| k (∀* p)    := p.max_idx_lt (k+1)
| k (∃* p)    := p.max_idx_lt (k+1)

@[fol] def closed (p : form) : Prop := p.max_idx_lt 0

instance dec_max_idx_lt : ∀ p : form, ∀ k, decidable (p.max_idx_lt k) :=
begin
  induce `[intro k, try {simp_fol}, try {apply_instance},
    try {apply @and.decidable _ _ _ _}, try {apply ih},
    try {apply ihp}, try {apply ihq}], 
end

instance dec_closed (p : form) : decidable (closed p) := p.dec_max_idx_lt 0

@[fol] def holds (M : model α) : (nat → α) → form → Prop 
| v ⊤*        := _root_.true
| v ⊥*        := _root_.false
| v (k ** ts) := 
      M.rels k (ts.map (term.val M v))
| v (¬* p)   := ¬(p.holds v) 
| v (p ∨* q) := (p.holds v) ∨ (q.holds v)
| v (p ∧* q) := (p.holds v) ∧ (q.holds v)
| v (∀* p)   := ∀ a : α, p.holds (a::v)
| v (∃* p)   := ∃ a : α, p.holds (a::v)

notation M `;` v `⊨` p := holds M v p 

def equiv (α p q) : Prop := 
∀ M : model α, ∀ v, ((M ; v ⊨ p) ↔ (M ; v ⊨ q))

def valid (α p) : Prop := 
∀ M : model α, ∀ v, (M ; v ⊨ p)

def sat (α p) : Prop := 
∃ M : model α, ∀ v, (M ; v ⊨ p)

def unsat (α p) : Prop := ¬ sat α p

def rvalid [inhabited α] : 
  list (bool × nat) → model α → form → Prop 
| []            M p := M ; (λ _, @inhabited.default _ _) ⊨ p
| ((tt,k)::ars) M p := ∀ r : arity α Prop k, p.rvalid ars (r.app_list :r: M) 
| ((ff,k)::ars) M p := ∀ f : arity α α k,    p.rvalid ars (f.app_list :f: M)

lemma rvalid_of_valid [inhabited α] {p} (h : valid α p) :
  ∀ {ars : list (bool × nat)} {M : model α}, rvalid ars M p
| [] M := by apply h
| ((b,k)::as) σ := 
  begin 
    cases b; simp [rvalid]; 
    intro r; apply rvalid_of_valid 
  end

lemma holds_iff_holds_of_max_idx_lt :
  ∀ (p : form) (M : model α) (v w : nat → α) k, p.max_idx_lt k → 
  (∀ m < k, v m = w m) → ((M ; v ⊨ p) ↔ (M ; w ⊨ p)) :=
begin
  induce_iff `[intros M v w m h1 h2, split_ands], trivial, trivial,
  { simp_fol, apply iff_of_eq (congr_arg _ _),
    apply list.map_eq_map_of_forall_mem_eq,
    intros t h4, apply term.val_eq_val_of_max_idx_lt,
    apply h1 _ h4, apply h2 },
  { apply ih; assumption },
  { apply ihp; assumption },
  { apply ihq; assumption },
  { apply ihp; assumption },
  { apply ihq; assumption },
  { apply ih, apply h1, intro n, cases n with n; intro h3, 
    refl, apply h2, rw ← nat.succ_lt_succ_iff, assumption },
  { apply ih, apply h1, intro n, cases n with n; intro h3, 
    refl, apply h2, rw ← nat.succ_lt_succ_iff, assumption }
end

lemma holds_iff_holds_of_closed :
  ∀ (M : model α) v w p, closed p →
  ((M ; v ⊨ p) ↔ (M ; w ⊨ p)) := 
begin
  intros M v w p h1, 
  apply holds_iff_holds_of_max_idx_lt,
  apply h1, intros m h2, cases h2
end

lemma valid_of_closed_of_unsat_neg [inhabited α] :
  ∀ {p : form}, closed p → unsat α (¬* p) → valid α p := 
begin
  simp only [valid, unsat, sat], intros p h1 h2 M v, 
  apply classical.by_contradiction, intro h3, 
  apply h2, refine ⟨M, _⟩, intro w, 
  rw holds_iff_holds_of_closed _ _ w _ h1 at h3, assumption, 
end

def fv_core : nat → form → list nat 
| k ⊤*        := []
| k ⊥*        := []
| k (m ** ts) := ⋃ (ts.map (term.fv k))
| k (¬* p)    := fv_core k p
| k (p ∧* q)  := list.union (fv_core k p) (fv_core k q)
| k (p ∨* q)  := list.union (fv_core k p) (fv_core k q)
| k (∀* p)    := fv_core (k+1) p
| k (∃* p)    := fv_core (k+1) p

def fv (p) := fv_core 0 p

def fresh_func_idx : form → nat 
| ⊤*        := 0
| ⊥*        := 0
| (m ** ts) := list.max (ts.map (term.fresh_func_idx))
| (¬* p)    := fresh_func_idx p
| (p ∧* q)  := max (fresh_func_idx p) (fresh_func_idx q)
| (p ∨* q)  := max (fresh_func_idx p) (fresh_func_idx q)
| (∀* p)    := fresh_func_idx p
| (∃* p)    := fresh_func_idx p

def subst : nat → term → form → form 
| k s ⊤*        := ⊤* 
| k s ⊥*        := ⊥* 
| k s (m ** ts) := m ** (ts.map (term.subst k s))
| k s (¬* p)    := ¬*(subst k s p) 
| k s (p ∨* q)  := (subst k s p) ∨* (subst k s q)
| k s (p ∧* q)  := (subst k s p) ∧* (subst k s q)
| k s (∀* p)    := ∀* (subst (k+1) s.incr_vdx p)
| k s (∃* p)    := ∃* (subst (k+1) s.incr_vdx p)

end form