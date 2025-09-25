-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def repeated_n_times (arr : List Int) : Option Int := sorry

theorem repeated_n_times_first_repeat {arr : List Int} {n : Int}
  (h : repeated_n_times arr = some n) :
  ∀ x : Int, x ∈ arr → x ≠ n → 
  (arr.take (arr.indexOf x)).count x ≤ 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
/-
info: 3
-/
-- #guard_msgs in
-- #eval repeated_n_times [1, 2, 3, 3]

/-
info: 2
-/
-- #guard_msgs in
-- #eval repeated_n_times [2, 1, 2, 5, 3, 2]

/-
info: 5
-/
-- #guard_msgs in
-- #eval repeated_n_times [5, 1, 5, 2, 5, 3, 5, 4]
-- </vc-theorems>