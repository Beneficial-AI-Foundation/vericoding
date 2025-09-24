-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_product (nums : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem max_product_two_elements (a b : Nat)
  (h1 : 2 ≤ a ∧ a ≤ 1000)
  (h2 : 2 ≤ b ∧ b ≤ 1000) :
  max_product [a, b] = (a-1) * (b-1) := sorry
-- </vc-theorems>