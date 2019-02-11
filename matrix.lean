import .vector 

variables {k m n p : nat} {α : Type} [ring α]

open tactic vector

def matrix (α : Type) [ring α] (m n : nat) : Type := vector (vector α n) m

namespace matrix

def add : ∀ {m n : nat}, matrix α m n → 
  matrix α m n →  matrix α m n 
| 0 n A B := nil 
| (m+1) n A B :=
  let A' : matrix α m n := A.tail in
  let B' : matrix α m n := B.tail in
  cons (A.head + B.head) (add A' B')

instance has_add : has_add (matrix α m n) := ⟨add⟩ 

def sub : ∀ {m n : nat}, matrix α m n → 
  matrix α m n →  matrix α m n 
| 0 n A B := nil 
| (m+1) n A B :=
  let A' : matrix α m n := A.tail in
  let B' : matrix α m n := B.tail in
  cons (A.head - B.head) (sub A' B')

instance has_sub : has_sub (matrix α m n) := ⟨sub⟩ 

def split_col : ∀ {m n}, matrix α m (n+1) → vector α m × matrix α m n 
| 0 n A := (nil,nil)
| (m+1) n A := 
  let (c,A') := split_col A.tail in
  (c.cons A.head.head, A'.cons A.head.tail)

def cons_col : ∀ {m n}, vector α m → matrix α m n → matrix α m (n+1) 
| 0 n x A     := nil
| (m+1) n x A := vector.cons (A.head.cons x.head) (cons_col x.tail A.tail)

def mul_vec : ∀ {k m}, matrix α k m → vector α m → vector α k 
| 0 _ _ _     := nil   
| (k+1) m A x := vector.cons (A.head ⬝ x) (mul_vec A.tail x)

def mul : ∀ {k m n : nat}, matrix α k m → matrix α m n → matrix α k n 
| k m 0 A B     := vector.repeat vector.nil k
| k m (n+1) A B := 
  let (x,B') := split_col B in 
  cons_col (mul_vec A x) (mul A B')

def pad_length [has_repr α] : ∀ {m n}, matrix α m n → nat 
| 0 n A := 0
| (m+1) n A := max A.head.pad_length (pad_length A.tail)
  
def repr_core [has_repr α] (l : nat) : ∀ {m n}, matrix α m n → string 
| 0 n A := ""
| (m+1) n A := row_to_string l A.head ++ "\n" ++ repr_core A.tail

def repr [has_repr α] (m n) (A : matrix α m n) : string :=
repr_core (pad_length A) A

instance has_repr [has_repr α] {m n} : has_repr (matrix α m n) := ⟨repr m n⟩   

meta instance has_to_format [has_repr α] {m n} : has_to_format (matrix α m n) := 
⟨λ A, A.repr m n⟩   

meta instance has_to_tactic_format [has_repr α] {m n} : 
  has_to_tactic_format (matrix α m n) := 
has_to_format_to_has_to_tactic_format _

end matrix