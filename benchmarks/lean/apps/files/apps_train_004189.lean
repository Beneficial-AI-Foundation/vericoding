-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
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

/-
info: [16, 27, 30, 60, 70, 72, 84]
-/
-- #guard_msgs in
-- #eval mult_primefactor_sum 10 100

/-
info: [84, 105, 150]
-/
-- #guard_msgs in
-- #eval mult_primefactor_sum 80 150

/-
info: [105, 150, 180]
-/
-- #guard_msgs in
-- #eval mult_primefactor_sum 90 200
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded