import data.vector .list .string

variables {α : Type} {k m n : nat}

namespace vector

def dot_prod [ring α] : ∀ {k}, vector α k → vector α k → α 
| 0 v w     := 0
| (k+1) v w := v.head * w.head + dot_prod v.tail w.tail
infix `⬝` := dot_prod

def pad_length [has_repr α] : ∀ {n}, vector α n → nat 
| 0 x := 0
| (n+1) x := max (has_repr.repr x.head).length x.tail.pad_length

def singleton (a : α) : vector α 1 := ⟨[a],rfl⟩ 

def add [has_add α] : ∀ {k : nat}, vector α k → vector α k → vector α k 
| 0 x y := nil 
| (k+1) x y :=
  let x' : vector α k := x.tail in
  let y' : vector α k := y.tail in
  cons (x.head + y.head) (add x' y')

instance has_add [has_add α] : has_add (vector α k) := ⟨add⟩ 

def sub [has_sub α] : ∀ {k : nat}, vector α k → vector α k → vector α k 
| 0 x y := nil 
| (k+1) x y :=
  let x' : vector α k := x.tail in
  let y' : vector α k := y.tail in
  cons (x.head - y.head) (sub x' y')

instance has_sub [has_sub α] : has_sub (vector α k) := ⟨sub⟩ 

def halve {k} (x : vector α (2^(k+1))) : 
  vector α (2^k) × vector α (2^k) := 
( ⟨x.val.take (2^k), 
  begin 
    rw [list.length_take, x.property, min_eq_left],
    rw [nat.pow_succ, nat.mul_succ], apply nat.le_add_left
  end⟩, 
  ⟨x.val.drop (2^k), 
  begin
    rw [list.length_drop, x.property, nat.pow_succ, 
      nat.mul_succ, nat.add_sub_cancel], simp
  end⟩ ) 

def double {k} : 
  (vector α (2^k) × vector α (2^k)) → vector α (2^(k+1)) 
| ⟨x,y⟩ := 
  ⟨x.val ++ y.val, 
   begin
     rw [list.length_append, x.property, y.property,
       nat.pow_succ, nat.mul_succ], simp
   end⟩ 

lemma double_halve {k} (x : vector α (2^(k+1))) :
  double (halve x) = x := 
begin
  apply vector.eq, simp [double, halve, to_list], 
  apply list.append_take_drop
end

end vector

def row_to_string [has_repr α] (l) : ∀ {n}, vector α n → string
| 0 x     := " |" 
| (n+1) x := 
  " | " ++ (has_repr.repr x.head).pad l ++ row_to_string x.tail




 #exit 

def split (m n) (x : vector α (m+n)) : (vector α m × vector α n) :=
( ⟨(x.val.split m).fst, list.length_fst_split _ n _ x.property⟩, 
  ⟨(x.val.split m).snd, list.length_snd_split _ n _ x.property⟩ )

lemma append_split (m n) (x : vector α (m+n)) :
  append (split m n x).fst (split m n x).snd = x :=
begin
  simp [split, append], apply vector.eq, 
  simp [to_list], apply list.append_split
end
