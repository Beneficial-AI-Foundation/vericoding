/-
Write a function that takes an array of numbers (integers for the tests) and a target number. It should find two different items in the array that, when added together, give the target value. The indices of these items should then be returned in a tuple like so: `(index1, index2)`.

For the purposes of this kata, some tests may have multiple answers; any valid solutions will be accepted.

The input will always be valid (numbers will be an array of length 2 or greater, and all of the items will be numbers; target will always be the sum of two different items from that array).

Based on: http://oj.leetcode.com/problems/two-sum/
-/

-- <vc-helpers>
-- </vc-helpers>

def two_sum (numbers : List Int) (target : Int) : Option (Nat × Nat) :=
sorry

theorem two_sum_correct_sum 
  (numbers : List Int) 
  (target : Int)
  (h : numbers.length ≥ 2)
  (result : Option (Nat × Nat))
  (hresult : result = two_sum numbers target) :
  result.map (fun (ij : Nat × Nat) => 
    numbers.get! ij.fst + numbers.get! ij.snd = target) = some true :=
sorry

theorem two_sum_exists_for_sum_of_elements
  (numbers : List Int)
  (h : numbers.length ≥ 2) :
  let target := numbers.get! 0 + numbers.get! 1
  let result := two_sum numbers target
  result.isSome ∧ 
  result.map (fun ij => numbers.get! ij.fst + numbers.get! ij.snd = target) = some true :=
sorry

theorem two_sum_different_indices
  (numbers : List Int)
  (h : numbers.length ≥ 2) :
  let target := numbers.get! 0 + numbers.get! 1
  let result := two_sum numbers target
  result.map (fun ij => ij.fst ≠ ij.snd) = some true :=
sorry

/-
info: (0, 2)
-/
-- #guard_msgs in
-- #eval two_sum [1, 2, 3] 4

/-
info: (1, 2)
-/
-- #guard_msgs in
-- #eval two_sum [1234, 5678, 9012] 14690

/-
info: (0, 1)
-/
-- #guard_msgs in
-- #eval two_sum [2, 2, 3] 4

-- Apps difficulty: introductory
-- Assurance level: guarded