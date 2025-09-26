-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_remaining_chocolates (m n : Nat) : Nat := sorry

theorem remaining_chocolates_positive (m n : Nat) 
    (h1 : m > 0) (h2 : n > 0) :
    calculate_remaining_chocolates m n > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem remaining_chocolates_even (m n : Nat) 
    (h1 : m > 0) (h2 : n > 0) :
    calculate_remaining_chocolates m n % 2 = 0 := sorry

theorem remaining_chocolates_upper_bound (m n : Nat) 
    (h1 : m > 0) (h2 : n > 0) :
    calculate_remaining_chocolates m n ≤ 2 * min m n := sorry 

theorem remaining_chocolates_divides (m n : Nat)
    (h1 : m > 0) (h2 : n > 0) :
    m % ((calculate_remaining_chocolates m n) / 2) = 0 ∧ 
    n % ((calculate_remaining_chocolates m n) / 2) = 0 := sorry

theorem equal_inputs (x : Nat) (h : x > 0) :
    calculate_remaining_chocolates x x = 2 * x := sorry
-- </vc-theorems>