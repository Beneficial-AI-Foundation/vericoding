-- <vc-preamble>
def ceil_div (a b : Nat) : Nat :=
  (a + b - 1) / b

def list_max (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | (x::xs) => List.foldl max x xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_smallest_divisor (nums : List Nat) (threshold : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_element_case {nums : List Nat} {threshold : Nat}
  (h1 : nums.length = 1)
  (h2 : threshold > 0)
  (h3 : ∀ x ∈ nums, 1 ≤ x ∧ x ≤ 1000000)
  (h4 : threshold ≤ 1000000) :
  find_smallest_divisor nums threshold = ceil_div nums[0] threshold :=
sorry

theorem result_bounded {nums : List Nat} {threshold : Nat}
  (h1 : nums.length > 0)
  (h2 : nums.length ≤ 10)
  (h3 : ∀ x ∈ nums, 1 ≤ x ∧ x ≤ 100)
  (h4 : 1 ≤ threshold ∧ threshold ≤ 100) :
  1 ≤ find_smallest_divisor nums threshold ∧
  find_smallest_divisor nums threshold ≤ list_max nums :=
sorry
-- </vc-theorems>