-- import .misc data.list.basic data.vector

variables {α β : Type}

def arity (α β : Type) : nat → Type
| 0     := β 
| (n+1) := α → arity n 

namespace arity

def app_list [inhabited β] : ∀ {k}, arity α β k → list α → β 
| 0 f []          := f
| 0 f (_::_)      := @inhabited.default _ _
| (k+1) f []      := @inhabited.default _ _
| (k+1) f (a::as) := app_list (f a) as


#exit

def set [inhabited β] : ∀ {k} m, (arity α β k) → arity α β m
| 0     0     f := f
| (k+1) 0     f := @inhabited.default β _
| 0 (m+1)     f := λ a, f.set m
| (k+1) (m+1) f := λ a, (f a).set m

lemma set_eq_self [inhabited β] : 
  ∀ k (f : arity α β k), f.set k = f 
| 0 f     := rfl
| (k+1) f := 
  begin
    simp [set], rw function.funext_iff,
    intro a, rw (set_eq_self k)
  end

def app [inhabited β] : ∀ {k}, (arity α β k) → list α → β 
| 0     f []      := f
| 0     f (_::_)  := f
| (k+1) f []      := @inhabited.default _ _
| (k+1) f (a::as) := app (f a) as 


#exit
  def app : ∀ {n}, (arity α β n) → ∀ (as : list α), as.length = n → β 
  | 0 f _ _ := f
  | (n+1) f [] h := by {exfalso, cases h}
  | (n+1) f (a::as) h := 
     app (f a) as (by {cases h, refl}) 

  --def app_arity_if (b : β) (mf : Σ m, arity α β m) (as: list α) : β :=
  --dite (mf.fst = as.length) 
  --  (λ h, app_arity mf.snd as h.symm) (λ _, b) 
--
--  lemma app_arity_if_eq (b1 b2 : β) (nf mg) (as1 as2 : list α) : 
--  b1 = b2 → nf = mg → as1 = as2 → 
--  app_arity_if b1 nf as1 = app_arity_if b2 mg as2 := 
--  begin intros h1 h2 h3, rw [h1, h2, h3] end
--
  def sum_app : (Σ n, arity α β n × vector α n) → β := 
  λ x, app x.snd.fst x.snd.snd.val x.snd.snd.property
 
  def sum_app_eq_app : 
  ∀ {n} {f :arity α β n} {as : list α} {h : as.length = n}, 
   sum_app (sigma.mk n ⟨f, (subtype.mk as h)⟩) = app f as h :=
  λ n f as h, refl _

  lemma app_eq_app {α β : Type} {n m : ℕ} (f : arity α β n) (g : arity α β m)
    (as1 as2 : list α) (h1 : list.length as1 = n) (h2 : list.length as2 = m)
    (heq1 : n = m) (heq2 : @eq.rec _ _ _ f m heq1 = g) 
    (heq3 : as1 = as2) : app f as1 h1 = app g as2 h2 :=
  begin
    repeat {rw [sum_app_eq_app.symm]}, 
    apply congr_arg _ (sigma.eq _ _), apply heq1,
    rw prod.eq_iff_fst_eq_snd_eq, simp, constructor,
    subst heq1, simp at *, apply heq2,
    subst heq1, simp at *, apply heq3
  end

end arity