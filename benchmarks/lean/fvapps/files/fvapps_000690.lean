-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Nat) (arr : List Nat) : Nat :=
  sorry

def find_max_gcd (arr : List Nat) : Nat :=
  sorry

def gcd_of_list (numbers : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_returns_valid : ∀ (n : Nat) (arr : List Nat),
  arr ≠ [] → solve n arr = arr.head! ∨ solve n arr = arr.getLast! :=
sorry

theorem solve_optimality : ∀ (n : Nat) (arr : List Nat),
  arr ≠ [] →
  (arr.length = 1 → solve n arr = arr.head!) ∧
  (arr.length > 1 → solve n arr ≥ arr.head! ∧ solve n arr ≥ arr.getLast!) :=
sorry
-- </vc-theorems>