-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_exponent (n p : Int) : Option Int :=
  sorry

def pow (x y : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_exponent_divides {n p : Int} (h1 : n ≥ 2) (h2 : p ≥ 2) :
  match get_exponent n p with
  | none => False
  | some k =>
    (k = 0 → n % p ≠ 0) ∧
    (k > 0 → n % (pow p k) = 0 ∧ n % (pow p (k + 1)) ≠ 0)
  :=
sorry

theorem get_exponent_nonnegative {n p : Int} (h1 : n ≥ 2) (h2 : p ≥ 2) :
  match get_exponent n p with
  | none => False
  | some k => k ≥ 0
  :=
sorry

theorem get_exponent_invalid_divisor {n p : Int} (h : p ≤ 1) :
  get_exponent n p = none :=
sorry

theorem get_exponent_prime_power {n p : Int} (h1 : n ≥ 2) (h2 : p = 2) :
  get_exponent (n * (pow p 5)) p = Option.some ((get_exponent n p).getD 0 + 5) :=
sorry
-- </vc-theorems>