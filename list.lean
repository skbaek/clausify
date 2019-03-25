import data.list.basic 

variables {α β : Type}

namespace list

lemma map_eq_map_of_forall_mem_eq {f g : α → β} : 
∀ {as}, (∀ a ∈ as, f a = g a) → map f as = map g as 
| [] h1 := rfl  
| (a::as) h1 := 
  begin 
    simp only [map], constructor,
    apply h1 _ (or.inl rfl),
    apply map_eq_map_of_forall_mem_eq,
    apply forall_mem_of_forall_mem_cons h1 
  end

def gen_union [decidable_eq α] : list (list α) → list α 
| []           := []
| [l]          := l 
| (l1::l2::ls) := l1 ∪ (gen_union (l2::ls))

notation `⋃` := gen_union

def max [has_zero α] [decidable_linear_order α] : list α → α  
| []      := 0
| (a::as) := _root_.max a as.max 

end list

#exit

lemma map_eq_map_of_funeq_over (P : α → Prop) {f g : α → β} : 
∀ as, (∀ a, P a → f a = g a) → (∀ a ∈ as, P a) → map f as = map g as 
| [] h1 h2 := rfl  
| (a::as) h1 h2 := 
  begin 
    simp, constructor, apply h1 _ (h2 a (or.inl rfl)),
    apply map_eq_map_of_funeq_over, apply h1,
    apply forall_mem_of_forall_mem_cons h2
  end


  def to_string_sep_core {α : Type} 
  (f : α → string) (s : string) : list α → string 
  | [] := "" 
  | [a] := f a 
  | (a::as) := f a ++ s ++ to_string_sep_core as
  
  def to_string_sep {α : Type} (s : string) 
    [has_to_string α] : list α → string := 
    to_string_sep_core has_to_string.to_string s
  
  def head_nonempty {α : Type} : Π (l : list α), l ≠ [] → α 
  | [] h := by {exfalso, exact (h rfl)}
  | (a::as) h := a
  
  -- def pull_core : nat → list α → option (α × list α) 
  -- | _ [] := none 
  -- | 0 (a::as) := some ⟨a,as⟩ 
  -- | (n+1) (a::as) := 
  --   match pull_core n as with 
  --   | none := none 
  --   | (some ⟨a',as'⟩) := (some ⟨a',a::as'⟩)
  --   end 
  -- 
  -- def pull (n as) : list α :=
  -- match pull_core n as with 
  -- | none := as 
  -- | (some ⟨a,as'⟩) := (a::as')
  -- end
  
  def pull : nat → list α → list α 
  | _ [] := []
  | 0 as := as 
  | (n+1) (a::as) := 
    match pull n as with 
    | [] := a::as 
    | (a'::as') := a'::(a::as')
    end

  lemma pull_perm : ∀ n (as : list α), pull n as ~ as 
  | 0 [] := perm.refl _
  | 0 (a::as) := perm.refl _
  | (n+1) [] := perm.refl _
  | (n+1) (a::as) :=
    begin
      simp [pull], have ih := pull_perm n as,
      cases (pull n as) with a' as', apply perm.refl, 
      apply (perm.trans (perm.swap _ _ _) (perm.skip _ ih))
    end

  lemma mem_pull_iff {n a} {as : list α} :
  a ∈ pull n as ↔ a ∈ as :=
  mem_of_perm (pull_perm _ _)

  lemma pull_nil : ∀ n, pull n (nil : list α) = nil 
  | 0 := rfl
  | (n+1) := rfl
  
  def map_mems : Π (as : list α) (h : Π a ∈ as, β), list β 
  | [] _ := [] 
  | (a::as) h := 
    (h a (or.inl rfl))::(map_mems as (λ a' h', h a' (or.inr h')))

  lemma map_mems_length_eq : ∀ (as : list α) (h : Π a ∈ as, β), 
    (map_mems as h).length = as.length 
  | [] _ := rfl 
  | (a::as) h := 
    by { simp [map_mems], rw [map_mems_length_eq] }
  
  def cond_map {C : α → Type} (f : Π a, C a → β) : Π (as : list α), (Π a ∈ as, C a) → list β 
  | [] _ := []
  | (a::as) h := 
    (f a (h _ (or.inl rfl)))::(cond_map as (λ a' h', h _ (or.inr h')))
  
  lemma cond_map_length_eq {C : α → Type} (f : Π a, C a → β) :
    Π (as : list α) (h : Π a ∈ as, C a), (cond_map f as h).length = as.length 
  | [] _ := rfl
  | (a::as) h := 
    by { simp [cond_map], rw [cond_map_length_eq] }

  theorem forall_mem_nil' (C : α → Type) : ∀ x ∈ @nil α, C x :=
  λ _ h, by cases h

  lemma nth_append_ge : 
  ∀ {as1 : list α} {m}, as1.length = m → ∀ (as2 n), nth (as1 ++ as2) (m + n) = nth as2 n 
  | [] (m+1) h _ _ := by {cases h} 
  | [] 0 h as2 n := by {rw [nil_append, zero_add]}
  | (a1::as1) 0 h _ _:= by {cases h} 
  | (a1::as1) (m+1) h as2 n:=
    begin
      rw [add_comm (m+1) n, (add_assoc n m 1).symm, (nat.succ_eq_add_one (n+m)).symm], 
      simp at *, rw (add_comm 1 _) at h,
      apply (nth_append_ge (eq_of_add_eq_add_right h)), 
    end

  lemma nth_append_lt : 
  ∀ {as1 : list α} {n}, n < as1.length → ∀ as2, nth (as1 ++ as2) n = nth as1 n 
  | [] _ h _ := by {cases h}
  | (a1::as1) 0 _ _ := eq.refl _
  | (a1::as1) (n+1) h as2 :=
    begin
      apply @nth_append_lt as1 n _ as2, simp at h,
      rw add_comm 1 _ at h, apply nat.lt_of_succ_lt_succ, 
      repeat {rw nat.succ_eq_add_one}, assumption
    end 
  
  lemma map_eq_map_of_funeq {f g : α → β} (h : ∀ a, f a = g a) :
  ∀ as, map f as = map g as 
  | [] := rfl 
  | (a::as) := by {simp, constructor, apply h, apply map_eq_map_of_funeq}

  
  def pad_update_nth [inhabited α] : list α → ℕ → α → list α
  | (x::xs) 0     a := a :: xs
  | (x::xs) (i+1) a := x :: pad_update_nth xs i a
  | []      0     a := [a]
  | []      (i+1) a := (default α) :: pad_update_nth [] i a

  -- lemma nth_pad_update_nth [inhabited α] (as : list α) (k a) :
  -- nth (pad_update_nth as k a) k = some a := sorry

  lemma map_comp {f : β → γ} {g : α → β} {as} : 
  map (f ∘ g) as = map f (map g as) := by simp

end list

