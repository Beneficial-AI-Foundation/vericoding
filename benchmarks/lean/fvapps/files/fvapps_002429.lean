-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_ugly (n : Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem negative_and_zero_not_ugly {x : Int} (h : x ≤ 0) : 
  is_ugly x = false := 
  sorry

theorem products_of_2_3_5_are_ugly {x : Int} (h : x > 0) :
  is_ugly x = true ↔ ∃ a b c : Nat, x = 2^a * 3^b * 5^c :=
  sorry

theorem primes_except_2_3_5_not_ugly {p : Int} 
  (h1 : p > 0) 
  (h2 : p ≠ 2) 
  (h3 : p ≠ 3) 
  (h4 : p ≠ 5)
  (h5 : ∀ m : Int, 2 ≤ m → m < p → p % m ≠ 0) :
  is_ugly p = false :=
  sorry
-- </vc-theorems>