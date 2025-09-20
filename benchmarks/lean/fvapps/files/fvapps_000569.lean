-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def gcd (a b : Nat) : Nat :=
  sorry

def solve_evil_sorcerer (n : Nat) (p : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_evil_sorcerer_properties {n : Nat} {p : List Nat}
  (n_pos : n > 0) (p_pos : ∀ x ∈ p, x > 0) :
  let result := solve_evil_sorcerer n p

  result ≥ 0 ∧

  result ≤ n := by
  sorry

theorem gcd_properties {a b : Nat} (a_pos : a > 0) (b_pos : b > 0) :
  let g := gcd a b

  (a % g = 0 ∧ b % g = 0) ∧

  g > 0 ∧

  ∀ i, g < i → i ≤ min a b → ¬(a % i = 0 ∧ b % i = 0) := by
  sorry
-- </vc-theorems>