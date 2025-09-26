-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def swap (arr : Array Int) (i j : Int) : Array Int :=
sorry

def count (arr : Array Int) (value : Int) : Nat :=
sorry

def MoveZeroesToEnd (arr : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem swap_spec (arr : Array Int) (i j : Nat) :
arr.size > 0 ∧
0 ≤ i ∧ i < arr.size ∧
0 ≤ j ∧ j < arr.size →
let arr' := swap arr i j
arr'[i]! = arr[j]! ∧
arr'[j]! = arr[i]! ∧
(∀ k, 0 ≤ k ∧ k < arr.size ∧ k ≠ i ∧ k ≠ j → arr'[k]! = arr[k]!) :=
sorry

theorem count_spec (arr : Array Int) (value : Int) :
count arr value ≤ arr.size :=
sorry

theorem MoveZeroesToEnd_spec (arr : Array Int) :
arr.size ≥ 2 →
let arr' := MoveZeroesToEnd arr

-- Same size

arr'.size = arr.size ∧

-- Zeros to the right of first zero

(∀ i j, 0 ≤ i ∧ i < j ∧ j < arr'.size ∧ arr'[i]! = 0 → arr'[j]! = 0) ∧

-- Relative order of non-zero elements preserved

(∀ n m, 0 ≤ n ∧ n < m ∧ m < arr.size ∧ arr[n]! ≠ 0 ∧ arr[m]! ≠ 0 →

∃ k l, 0 ≤ k ∧ k < l ∧ l < arr'.size ∧

arr'[k]! = arr[n]! ∧

arr'[l]! = arr[m]!) :=
sorry
-- </vc-theorems>