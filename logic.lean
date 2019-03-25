import logic.basic

variable {α : Type}

lemma forall_iff_forall {P Q : α → Prop} : 
  (∀ a, P a ↔ Q a) → ((∀ a, P a) ↔ (∀ a, Q a)) :=
λ h, iff.intro 
  (λ hP a, (h a).elim_left (hP _)) 
  (λ hQ a, (h a).elim_right (hQ _)) 

lemma exists_iff_exists {P Q : α → Prop} : 
  (∀ a, P a ↔ Q a) → ((∃ a, P a) ↔ (∃ a, Q a)) := 
λ h, iff.intro 
  (λ hP, begin cases hP with a ha, existsi a, apply (h a).elim_left ha end) 
  (λ hQ, begin cases hQ with a ha, existsi a, apply (h a).elim_right ha end) 

lemma or_iff_or {p p' q q' : Prop} :
  (p ↔ p') → (q ↔ q') → ((p ∨ q) ↔ (p' ∨ q')) := 
begin
  intros hp hq, rewrite hp, rewrite hq
end

lemma and_iff_and {p p' q q' : Prop} :
  (p ↔ p') → (q ↔ q') → ((p ∧ q) ↔ (p' ∧ q')) := 
begin intros hp hq, rewrite hp, rewrite hq end

lemma imp_of_imp (p) {q} : (p → q) → (p → q) := id

#exit
lemma not_true.elim : Π {C : Sort u}, ¬ true → C :=
λ _ h, false.elim (h trivial)

lemma not_and.elim : 
  ∀ {a b c : Prop}, ¬(a ∧ b) → (¬a → c) → (¬b → c) → c :=
begin
  intros a b c h1 h2 h3, 
  cases (@classical.or_not a) with ha ha,
  apply (h3 $ λ hb, h1 ⟨ha,hb⟩), apply h2 ha
end

lemma not_or.elim
  : ∀ {a b c : Prop}, ¬(a ∨ b) → (¬a → ¬b → c) → c :=
begin
  intros a b c h1 h2, rw not_or_distrib at h1,
  cases h1, apply h2; assumption
end

lemma imp.elim : 
  ∀ {a b c : Prop}, (a → b) → (¬a → c) → (b → c) → c :=
begin
  intros a b c h1 h2 h3, 
  cases (@classical.or_not a) with ha ha,
  apply (h3 $ h1 ha), apply h2 ha
end

lemma not_imp.elim
  : ∀ {a b c : Prop}, ¬(a → b) → (a → ¬b → c) → c :=
begin
  intros a b c h1 h2, 
  cases (@classical.or_not b) with hb hb,
  exfalso, apply (h1 $ λ _, hb),
  cases (@classical.or_not a) with ha ha,
  apply (h2 ha hb), exfalso, 
  apply (h1 $ λ ha', false.elim $ ha ha'),
end

lemma not_forall.elim : 
  ∀ {α : Sort u} {p : α → Prop} {b : Prop}, 
  (¬ ∀ (x : α), p x) → (∀ (a : α), (¬ p a) → b) → b :=
begin
  intros α p b h1 h2, rw classical.not_forall at h1,
  cases h1 with a ha, apply h2 _ ha
end

variables {p q : Prop}

lemma not_or_not_of_not_and : 
  ¬ (p ∧ q) → (¬ p ∨ ¬ q) :=
λ h, @classical.by_cases p (¬ p ∨ ¬ q) 
  (λ hp, or.inr (λ hq, h $ and.intro hp hq)) 
  (λ hnp, or.inl hnp)

lemma not_or_left : ¬ (p ∨ q) → ¬ p :=
λ h, (not_or_distrib.elim_left h).left

lemma not_or_right : ¬ (p ∨ q) → ¬ q :=
λ h, (not_or_distrib.elim_left h).right

lemma not_or_of_imp_cls : (p → q) → ¬p ∨ q := 
@not_or_of_imp p q (classical.dec p) 

lemma not_imp_left : ¬ (p → q) → p :=
λ h, ((@not_imp _ _ (classical.dec _)).elim_left h).left

lemma not_imp_right : ¬ (p → q) → ¬ q :=
λ h, ((@not_imp _ _ (classical.dec _)).elim_left h).right

lemma iff_of_left_of_right : p → q → (p ↔ q) := 
λ hp hq, iff.intro (λ _, hq) (λ _, hp)

variables {α : Type}
