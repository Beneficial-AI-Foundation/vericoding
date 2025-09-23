-- <vc-preamble>
def List.sorted : List Nat → Bool
| [] => true
| [_] => true
| x :: y :: xs => x ≤ y ∧ sorted (y :: xs)

def applyFlips : List Nat → List Nat → List Nat
| xs, [] => xs
| xs, k::ks => applyFlips ((xs.take k).reverse ++ xs.drop k) ks
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pancakeSort : List Nat → List Nat
| xs =>
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pancakeSort_produces_valid_flips (arr : List Nat) :
  ∀ k ∈ pancakeSort arr, 1 ≤ k ∧ k ≤ arr.length :=
sorry

theorem pancakeSort_sorts (arr : List Nat) :
  (applyFlips arr (pancakeSort arr)).sorted :=
sorry

theorem pancakeSort_on_sorted_is_empty (arr : List Nat) :
  arr.sorted → pancakeSort arr = [] :=
sorry

theorem pancakeSort_reverses_reversed (arr : List Nat) :
  arr = arr.reverse →
  (applyFlips arr (pancakeSort arr)).sorted :=
sorry
-- </vc-theorems>