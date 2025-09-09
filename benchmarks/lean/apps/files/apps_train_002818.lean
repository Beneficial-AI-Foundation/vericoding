-- <vc-helpers>
-- </vc-helpers>

def divisible_by (numbers : List Int) (divisor : Int) : List Int :=
  sorry

theorem divisible_by_contains_only_input_elements (numbers : List Int) (divisor : Int) 
    (h : divisor ≠ 0) :
  ∀ x, x ∈ divisible_by numbers divisor → x ∈ numbers := by
  sorry

theorem divisible_by_all_divisible (numbers : List Int) (divisor : Int) 
    (h : divisor ≠ 0) :
  ∀ x, x ∈ divisible_by numbers divisor → x % divisor = 0 := by
  sorry

theorem divisible_by_contains_all_divisible (numbers : List Int) (divisor : Int)
    (h : divisor ≠ 0) :
  ∀ x, x ∈ numbers → x % divisor = 0 → x ∈ divisible_by numbers divisor := by
  sorry

theorem divisible_by_length (numbers : List Int) (divisor : Int)
    (h : divisor ≠ 0) :
  (divisible_by numbers divisor).length ≤ numbers.length := by
  sorry

theorem divisible_by_one (numbers : List Int) :
  divisible_by numbers 1 = numbers := by
  sorry

/-
info: [2, 4, 6]
-/
-- #guard_msgs in
-- #eval divisible_by [1, 2, 3, 4, 5, 6] 2

/-
info: [3, 6]
-/
-- #guard_msgs in
-- #eval divisible_by [1, 2, 3, 4, 5, 6] 3

/-
info: []
-/
-- #guard_msgs in
-- #eval divisible_by [1, 3, 5] 2

-- Apps difficulty: introductory
-- Assurance level: guarded