-- <vc-preamble>
def List.firstElem (l : List Nat) (h : l.length > 0) : Nat :=
  match l with
  | [] => by contradiction
  | x::_ => x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def gcd (a b : Nat) : Nat :=
  sorry

def find_largest_gcd_1_subarray (arr : List Nat) : Int :=
  sorry

def reduce_gcd (l : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem gcd_one_returns_full_length {arr : List Nat} (h1 : arr.length ≥ 2) (h2 : ∀ x ∈ arr, x ≥ 1)
    (h3 : reduce_gcd arr = 1) :
  find_largest_gcd_1_subarray arr = arr.length :=
sorry

theorem non_gcd_one_returns_negative {arr : List Nat} (h1 : arr.length ≥ 2) (h2 : ∀ x ∈ arr, x ≥ 1)
    (h3 : reduce_gcd arr > 1) :
  find_largest_gcd_1_subarray arr = -1 :=
sorry

theorem return_bounds {arr : List Nat} (h1 : arr.length ≥ 2) (h2 : ∀ x ∈ arr, x ≥ 2) :
  find_largest_gcd_1_subarray arr = -1 ∨
  (1 ≤ find_largest_gcd_1_subarray arr ∧ find_largest_gcd_1_subarray arr ≤ arr.length) :=
sorry

theorem same_elements_no_gcd_one {arr : List Nat} (h1 : arr.length ≥ 2)
    (h2 : ∀ x ∈ arr, ∀ y ∈ arr, x = y) :
  ∀ x ∈ arr, x ≠ 1 → find_largest_gcd_1_subarray arr = -1 :=
sorry
-- </vc-theorems>