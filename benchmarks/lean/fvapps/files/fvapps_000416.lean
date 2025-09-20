-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reordered_power_of_2 (n : Nat) : Bool :=
sorry

def get_powers_of_2 (max_digits : Nat) : List Nat :=
sorry

def digits (n : Nat) : List Nat :=
sorry

def sorted_digits (n : Nat) : List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem power_2_permutations_property {n : Nat} (h : reordered_power_of_2 n = true) :
  ∃ p, (p = 2^(Nat.log2 p)) ∧ sorted_digits n = sorted_digits p :=
sorry

theorem single_digit_property {n : Nat} (h : List.length (digits n) = 1) :
  reordered_power_of_2 n = (n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8) :=
sorry

theorem leading_zeros_property {n : Nat} (h : n < 10) :
  reordered_power_of_2 n = reordered_power_of_2 (10 * n) :=
sorry
-- </vc-theorems>