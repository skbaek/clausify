
namespace nat

lemma succ_lt_succ_iff : 
  ∀ {a b : ℕ}, nat.succ a < nat.succ b ↔ a < b :=
begin
  intros a b, apply iff.intro,
  apply lt_of_succ_lt_succ,
  apply succ_lt_succ
end

end nat