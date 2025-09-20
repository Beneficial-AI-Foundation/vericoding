-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def factorize_add (n : Nat) : Nat := sorry 

def mult_primefactor_sum (a b : Nat) : List Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem factorize_add_le (n : Nat) (h : n > 0) : 
  factorize_add n ≤ n := sorry

theorem factorize_add_pos (n : Nat) (h : n > 0) :
  factorize_add n > 0 := sorry

theorem mult_primefactor_sum_in_range (a b x : Nat) (h : x ∈ mult_primefactor_sum a b) :
  min a b ≤ x ∧ x ≤ max a b := sorry

theorem mult_primefactor_sum_ordered (a b i j : Nat) 
  (h1 : i < j) (h2 : j < (mult_primefactor_sum a b).length) :
  (mult_primefactor_sum a b)[i] < (mult_primefactor_sum a b)[j] := sorry

theorem mult_primefactor_sum_divisible (a b x : Nat) 
  (h : x ∈ mult_primefactor_sum a b) :
  x % factorize_add x = 0 := sorry

theorem mult_primefactor_sum_not_equal (a b x : Nat)
  (h : x ∈ mult_primefactor_sum a b) :
  factorize_add x ≠ x := sorry
-- </vc-theorems>