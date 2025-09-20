-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_num (arr : List Nat) : List Nat :=
sorry

def is_prime (n : Nat) : Bool :=
sorry

def minimum (l : List Nat) (h : l.length > 0) : Nat :=
sorry

def product (l : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_num_basic_properties {arr : List Nat} (h1 : arr.length > 0)
  (h2 : ∀ x ∈ arr, 2 ≤ x ∧ x ≤ 20) :
  let result := get_num arr
  result.length = 4 ∧
  result[0]! = product arr ∧
  result[2]! = minimum arr h1 ∧
  result[3]! = result[0]! / result[2]! :=
sorry

theorem get_num_small_factors {arr : List Nat}
  (h1 : 2 ≤ arr.length ∧ arr.length ≤ 3)
  (h2 : ∀ x ∈ arr, 2 ≤ x ∧ x ≤ 7) :
  let result := get_num arr
  result[0]! > 0 ∧
  result[1]! ≥ 0 ∧
  result[2]! ≤ minimum arr (by exact Nat.zero_lt_of_lt h1.left) ∧
  result[0]! % result[2]! = 0 :=
sorry
-- </vc-theorems>