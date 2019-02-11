import data.num.lemmas .matrix .strassen

open vector matrix tactic

def zero_mat : ∀ k, matrix znum (2^k) (2^k)
| 0 := vector.singleton (vector.singleton 1)
| (k+1) := quadruple (zero_mat k, zero_mat k, zero_mat k, zero_mat k)

def arith_prog : ∀ k, vector znum k  
| 0     := nil
| (k+1) := cons k (arith_prog k) 

def arith_row (k : nat) : vector znum (2^k) := arith_prog (2^k)

def arith_mat (k : nat) : matrix znum (2^k) (2^k) :=
vector.repeat (arith_row k) (2^k) 

def size : nat := 7

def test_mat := arith_mat size

def test := mul test_mat test_mat

set_option profiler true

#eval test

#exit
def test2 := strassen 2 test_mat test_mat
def test3 := strassen 3 test_mat test_mat
def test4 := strassen 4 test_mat test_mat
def test5 := strassen 5 test_mat test_mat
def test6 := strassen 6 test_mat test_mat
def test7 := strassen 7 test_mat test_mat


#eval test2
#eval test3
#eval test4
#eval test5
#eval test6
#eval test7
#eval test
