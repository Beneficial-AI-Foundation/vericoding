-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def checkConcatenatedSum (n : Int) (r : Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem non_positive_repeat_is_false {n r : Int} 
  (h : r ≤ 0) : checkConcatenatedSum n r = false :=
  sorry

theorem check_symmetry {n r : Int}
  (h : r > 0) (h2 : r ≤ 10) :
  checkConcatenatedSum n r = checkConcatenatedSum (-n) r :=
  sorry

theorem zero_is_true {r : Int}
  (h : r > 0) (h2 : r ≤ 10) :
  checkConcatenatedSum 0 r = true :=
  sorry

theorem large_sum_is_false {n r : Int}
  (h_pos : n > 0) (h_r : r > 1) (h_r2 : r ≤ 10)
  (digitSum : Nat)
  (h_sum : digitSum > 1)
  (h_digits : digitSum = sorry) :
  checkConcatenatedSum n r = false :=
  sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval check_concatenated_sum 2997 3

/-
info: True
-/
-- #guard_msgs in
-- #eval check_concatenated_sum -198 2

/-
info: False
-/
-- #guard_msgs in
-- #eval check_concatenated_sum 198 0
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded