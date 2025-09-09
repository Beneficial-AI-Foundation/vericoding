def isArithmeticSequence (arr : List Int) : Bool :=
  sorry

def sumOfRegularNumbers (arr : List Int) : Int :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def sum (l : List Int) : Int :=
  sorry

theorem regular_numbers_properties {arr : List Int} (h : arr.length ≥ 3) :
  let result := sumOfRegularNumbers arr
  (result ≥ 0 ∨ (result < 0 ∧ ∃ x ∈ arr, x < 0)) ∧
  (result ≠ 0 → ∃ i, i + 2 < arr.length ∧ 
    isArithmeticSequence (arr.take 3))
  :=
sorry

theorem three_element_sequence {arr : List Int} (h : arr.length = 3) :
  let d₁ := arr[0]! - arr[1]!
  let d₂ := arr[1]! - arr[2]!
  d₁ = d₂ → sumOfRegularNumbers arr = sum arr ∧
  d₁ ≠ d₂ → sumOfRegularNumbers arr = 0 :=
sorry

theorem non_overlapping_sequences {arr : List Int} (h : arr.length ≥ 4) :
  let result := sumOfRegularNumbers arr
  result > 0 →
  ∃ i, i + 2 < arr.length ∧
  (arr[i]! - arr[i+1]! = arr[i+1]! - arr[i+2]!) :=
sorry

/-
info: 639
-/
-- #guard_msgs in
-- #eval sum_of_regular_numbers [54, 70, 86, 1, -2, -5, 0, 5, 78, 145, 212, 15]

/-
info: 1200
-/
-- #guard_msgs in
-- #eval sum_of_regular_numbers [7, 2, 3, 2, -2, 400, 802]

/-
info: -13994
-/
-- #guard_msgs in
-- #eval sum_of_regular_numbers [-1, 7000, 1, -6998, -13997]

-- Apps difficulty: introductory
-- Assurance level: unguarded