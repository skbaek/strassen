import data.num.lemmas .matrix .strassen

open vector matrix tactic

def const_mat (c : int) : ∀ k, matrix int (2^k) (2^k)
| 0 := vector.singleton (vector.singleton c)
| (k+1) := quadruple (const_mat k, const_mat k, const_mat k, const_mat k)

def arith_prog : ∀ k m : nat, vector int m
| k 0     := nil 
| k (m+1) := cons k (arith_prog (k+1) m)

def arith_prog_mat_core : ∀ k m n : nat, matrix int m n
| k 0     n := nil
| k (m+1) n := cons (arith_prog k n) (arith_prog_mat_core (k+1) m n) 

def arith_prog_mat (m : nat) : matrix int (2^m) (2^m) := 
arith_prog_mat_core 0 (2^m) (2^m) 

def fib_vec : ∀ k : nat, ∀ i j : int, vector int k 
| 0 _ _     := nil
| (k+1) i j := (i+j)::(fib_vec k j (i+j))

def fib_mat_core : ∀ m n : nat, ∀ i j : int, matrix int m (n+2)
| 0     _ _ _ := nil
| (m+1) n i j := (i::j::fib_vec n i j)::(fib_mat_core m n j (i+j))

def fib_mat (m : nat) : matrix int (2^m) (2^m) := 
match (2^m) with 
| 0 := nil 
| 1 := matrix.singleton 1 
| (n+2) := fib_mat_core (n+2) n 1 1
end

def size : nat := 6

def test_mat := matrix.map (λ x, (100000 : int) * x) (arith_prog_mat size)

def test  := mul test_mat test_mat
def test2 := strassen 2 test_mat test_mat
def test3 := strassen 3 test_mat test_mat
def test4 := strassen 4 test_mat test_mat
def test5 := strassen 5 test_mat test_mat
def test6 := strassen 6 test_mat test_mat
def test7 := strassen 7 test_mat test_mat

set_option profiler true

#eval test2
#eval test3
#eval test4
#eval test5
#eval test6
#eval test7
#eval test
