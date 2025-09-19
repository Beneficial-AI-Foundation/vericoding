-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (nums : List Nat) : Nat :=
sorry

def sums (l : List Nat) : List Nat :=
sorry

def findMin (s : List Nat) : Nat :=
sorry

def sortList (l : List Nat) : List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_returns_positive (nums : List Nat)
  (h : ∀ x ∈ nums, x > 0 ∧ x ≤ 1000)
  : solve nums > 0 :=
sorry

theorem solve_order_invariant (nums : List Nat)
  (h : ∀ x ∈ nums, x > 0 ∧ x ≤ 100)
  : solve nums = solve (sortList nums) :=
sorry

theorem solve_is_min_missing_sum {nums : List Nat}
  (h : ∀ x ∈ nums, x > 0 ∧ x ≤ 10)
  (h2 : nums.length ≤ 5)
  : solve nums = findMin (sums nums) :=
sorry
-- </vc-theorems>