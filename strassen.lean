import .matrix

variables {k m n p : nat} {α : Type} [ring α]

open vector

namespace matrix

def halve_rows {k} : 
  matrix α (2^(k+1)) m →  
  (matrix α (2^k) m × matrix α (2^k) m) := vector.halve  

def halve_cols {k} : 
  ∀ {m}, matrix α m (2^(k+1)) →  
  ( matrix α m (2^k) ×  matrix α m (2^k) ) 
| 0 A := (nil,nil)  
| (m+1) A :=
  let (x₁,x₂) := A.head.halve in 
  let (A₁,A₂) := halve_cols A.tail in 
  (cons x₁ A₁, cons x₂ A₂)

def quadrisect {k} (A : matrix α (2^(k+1)) (2^(k+1))) :
  ( matrix α (2^k) (2^k) × matrix α (2^k) (2^k) × 
    matrix α (2^k) (2^k) × matrix α (2^k) (2^k) ) := 
let (A₁,A₂) := halve_rows A in 
let (A₁₁,A₁₂) := halve_cols A₁ in 
let (A₂₁,A₂₂) := halve_cols A₂ in 
(A₁₁,A₁₂,A₂₁,A₂₂) 

def double_rows :
  (matrix α (2^k) n × matrix α (2^k) n) →  
  matrix α (2^(k+1)) n := vector.double

def double_cols :
  ∀ {m}, (matrix α m (2^k) × matrix α m (2^k)) →  
  matrix α m (2^(k+1)) 
| 0 ⟨A,B⟩ := nil
| (m+1) ⟨A,B⟩ := 
  cons (vector.double (A.head, B.head)) 
    (double_cols ⟨A.tail,B.tail⟩)

def quadruple {k : nat} : 
  ( matrix α (2^k) (2^k) × matrix α (2^k) (2^k) × 
    matrix α (2^k) (2^k) × matrix α (2^k) (2^k) ) → 
  matrix α (2^(k+1)) (2^(k+1)) 
| ⟨A₁₁,A₁₂,A₂₁,A₂₂⟩ := 
  double_rows (double_cols ⟨A₁₁,A₁₂⟩, double_cols ⟨A₂₁,A₂₂⟩) 

def strassen (t : nat) : 
  ∀ {k : nat}, matrix α (2^k) (2^k) → 
  matrix α (2^k) (2^k) → matrix α (2^k) (2^k) 
| 0 A B := mul A B
| (k+1) A B :=
  if k < t 
  then mul A B 
  else 
  let (A₁₁, A₁₂, A₂₁, A₂₂) := quadrisect A in
  let (B₁₁, B₁₂, B₂₁, B₂₂) := quadrisect B in
  let S₁ := A₂₁ + A₂₂ in
  let S₂ := S₁ - A₁₁ in
  let S₃ := A₁₁ - A₂₁ in
  let S₄ := A₁₂ - S₂ in
  let T₁ := B₁₂ - B₁₁ in
  let T₂ := B₂₂ - T₁ in
  let T₃ := B₂₂ - B₁₂ in
  let T₄ := T₂ - B₂₁ in
  let P₁ := strassen A₁₁ B₁₁ in
  let P₂ := strassen A₁₂ B₂₁ in
  let P₃ := strassen S₄ B₂₂ in
  let P₄ := strassen A₂₂ T₄ in
  let P₅ := strassen S₁ T₁ in
  let P₆ := strassen S₂ T₂ in
  let P₇ := strassen S₃ T₃ in
  let U₁ := P₁ + P₂ in
  let U₂ := P₁ + P₆ in
  let U₃ := U₂ + P₇ in
  let U₄ := U₂ + P₅ in
  let U₅ := U₄ + P₃ in
  let U₆ := U₃ - P₄ in
  let U₇ := U₃ + P₅ in
  quadruple (U₁,U₅,U₆,U₇) 

end matrix