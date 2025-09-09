def min_and_max (l d x : Nat) : List Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def sum_of_digits (n : Nat) : Nat :=
  sorry

theorem min_and_max_properties {l d x : Nat}
  (h1: l ≤ d) 
  (h2: l > 0)
  (h3: d ≤ 1000)
  (h4: x ≤ 27)
  (h5: ∃ n, l ≤ n ∧ n ≤ d ∧ sum_of_digits n = x) :
  let result := min_and_max l d x
  List.length result = 2 ∧
  result[0]! ≤ result[1]! ∧
  l ≤ result[0]! ∧ result[0]! ≤ d ∧
  l ≤ result[1]! ∧ result[1]! ≤ d ∧
  sum_of_digits result[0]! = x ∧
  sum_of_digits result[1]! = x :=
  sorry

theorem min_and_max_identical_bounds {n : Nat}
  (h1: n > 0)
  (h2: n ≤ 1000) :
  let x := sum_of_digits n
  let result := min_and_max n n x
  result[0]! = n ∧ result[1]! = n :=
  sorry

/-
info: [109, 190]
-/
-- #guard_msgs in
-- #eval min_and_max 100 200 10

/-
info: [505, 505]
-/
-- #guard_msgs in
-- #eval min_and_max 500 505 10

/-
info: [104, 500]
-/
-- #guard_msgs in
-- #eval min_and_max 99 501 5

-- Apps difficulty: introductory
-- Assurance level: guarded