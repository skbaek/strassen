namespace list

variables {α : Type}



lemma append_take_drop : 
  ∀ k (as : list α), as.take k ++ as.drop k = as 
| 0 as := rfl
| k [] := begin cases k; simp end
| (k+1) (a::as) := 
  begin simp [append_take_drop] end


#exit
def split : nat → list α → (list α × list α) 
| 0 []          := ([],[])
| (k+1) []      := ([],[])
| 0     (a::as) := ⟨[], a::as⟩ 
| (k+1) (a::as) := let (as1,as2) := as.split k in (a::as1,as2)

lemma split_succ_cons (k a) (as : list α) :
  split (k+1) (a::as) = (a::(split k as).fst, (split k as).snd) := 
begin simp only [split], cases (split k as) with as1 as2, refl end

lemma append_split : ∀ (k) (as : list α), 
  (split k as).fst ++ (split k as).snd = as 
| k [] := begin cases k; refl end
| 0 as := begin cases as with a as; refl end
| (k+1) (a::as) :=
  begin rw split_succ_cons, simp [append_split] end

lemma length_fst_split : ∀ (m n) (as : list α),
  as.length = m + n → (split m as).fst.length = m 
| 0 n as h := begin cases as with a as; refl end
| (m+1) n as h :=
  begin
    cases as with a as, { simp at h, cases h },
    { rw split_succ_cons, simp, rw length_fst_split m n, simp,
      rw [length_cons, add_comm m 1, add_assoc, 
          nat.add_one, nat.one_add] at h,
      simp at h, assumption }
  end

lemma length_snd_split : ∀ (m n) (as : list α),
  as.length = m + n → (split m as).snd.length = n  
| 0 n [] h := begin  simp at h, simp [split], assumption end
| 0 n (a::as) h := begin simp at h, simp [split], assumption end
| (m+1) n [] h := begin simp at h, cases h end
| (m+1) n (a::as) h := 
  begin 
    simp at h, rw split_succ_cons, simp, apply length_snd_split,
    rw [← add_assoc, nat.add_one, nat.one_add] at h, simp at h,
    assumption
  end

end list