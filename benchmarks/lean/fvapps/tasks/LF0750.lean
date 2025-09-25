-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_gcd_pair (a b : Nat) : Nat := sorry

theorem gcd_positive (a b : Nat) (h1 : a > 0) (h2 : b > 0) : 
  let gcd := find_gcd_pair a b
  gcd > 0 ∧ a % gcd = 0 ∧ b % gcd = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem gcd_is_maximal (a b : Nat) (h1 : a > 0) (h2 : b > 0) :
  let gcd := find_gcd_pair a b
  ∀ d, d > gcd → d ≤ min a b → ¬(a % d = 0 ∧ b % d = 0) := sorry

theorem gcd_same_number (n : Nat) (h : n > 0) :
  find_gcd_pair n n = n := sorry
-- </vc-theorems>