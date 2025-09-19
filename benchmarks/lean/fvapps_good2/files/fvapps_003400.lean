-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def proc_seq : List Nat → List Nat
  | xs => sorry

def countPermNoLeadingZero (n : Nat) (m : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem proc_seq_valid_output (nums : List Nat) :
  let result := proc_seq nums
  (result.length = 2 ∨ result.length = 4) ∧
  (∀ x ∈ result, x ≥ 0) ∧
  (result.length = 2 → result.head! = 1) ∧
  (result.length = 4 →
    result[1]! ≤ result[2]! ∧ result[1]! ≤ result[3]!) :=
sorry

theorem proc_seq_leading_zeros (n : Nat) (h : n ≥ 100 ∧ n ≤ 999) :
  let result := proc_seq [n, 0]
  result.head! = countPermNoLeadingZero n 0 :=
sorry

theorem proc_seq_small_nums {nums : List Nat} (h : 2 ≤ nums.length ∧ nums.length ≤ 3)
  (h' : ∀ n ∈ nums, 1 ≤ n ∧ n ≤ 9) :
  let result := proc_seq nums
  (result.length = 2 ∨ result.length = 4) ∧
  (∀ x ∈ result, x ≥ 0) ∧
  (result.length = 2 → result.head! = 1) ∧
  (result.length = 4 →
    result[1]! ≤ result[2]! ∧ result[1]! ≤ result[3]!) :=
sorry
-- </vc-theorems>