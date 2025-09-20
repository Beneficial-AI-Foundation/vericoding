-- <vc-preamble>
def abs (x: Nat) (y: Nat) : Nat :=
if x ≥ y then x - y else y - x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_min_skill_diff (n: Nat) (arr: List Nat) : Nat :=
sorry

def list_max (xs: List Nat) : Nat :=
sorry

def list_min (xs: List Nat) : Nat :=
sorry

def list_sort (xs: List Nat) : List Nat :=
sorry

def list_differences (xs: List Nat) : List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_skill_diff_properties {n: Nat} {arr: List Nat} (h1: n < arr.length) (h2: 1 ≤ n) (h3: arr.length ≥ 2)
(h4: ∀ x ∈ arr, 1 ≤ x ∧ x ≤ 1000) :
  let result := solve_min_skill_diff n arr
  result ≥ 0 ∧ result ≤ list_max arr - list_min arr :=
sorry

theorem identical_values_property {arr: List Nat} (h1: arr.length ≥ 2)
(h2: ∀ x ∈ arr, x = 1) :
  let n := arr.length / 2
  solve_min_skill_diff n arr = 0 :=
sorry

theorem sorted_sequence_property {n: Nat} {arr: List Nat}
(h1: n < arr.length) (h2: 1 ≤ n) (h3: 2 ≤ arr.length) (h4: arr.length ≤ 20)
(h5: ∀ x ∈ arr, 1 ≤ x ∧ x ≤ 100) :
  let result := solve_min_skill_diff n arr
  let sorted := list_sort arr
  let diffs := list_differences sorted
  result ∈ diffs :=
sorry
-- </vc-theorems>