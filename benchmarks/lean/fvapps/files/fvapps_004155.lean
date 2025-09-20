-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def gcd (a b : Nat) : Nat := sorry

def fraction (a b : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem fraction_output_lower_bound {a b : Nat} (ha : a > 0) (hb : b > 0) :
  fraction a b ≥ 2 := sorry

theorem fraction_identity_cases {n : Nat} (hn : n > 0) :
  fraction n n = 2 := sorry
-- </vc-theorems>