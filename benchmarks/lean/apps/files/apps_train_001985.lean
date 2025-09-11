-- <vc-preamble>
def maximum (l : List Int) : Int :=
  sorry

def minimum (l : List Int) : Int :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_difference_sum (n k : Nat) (arr : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_difference_sum_non_negative 
  {n k : Nat} {arr : List Int}
  (h1 : n = arr.length)
  (h2 : k ≤ n)
  (h3 : n > 0) :
  min_difference_sum n k arr ≥ 0 := 
  sorry

theorem min_difference_sum_upper_bound
  {n k : Nat} {arr : List Int}
  (h1 : n = arr.length)
  (h2 : k ≤ n)
  (h3 : n > 0) :
  min_difference_sum n k arr ≤ (maximum arr - minimum arr) * k := 
  sorry

theorem min_difference_sum_k_equals_n
  {n k : Nat} {arr : List Int}
  (h1 : n = arr.length)
  (h2 : k = n)
  (h3 : n > 0) :
  min_difference_sum n k arr = 0 :=
  sorry

theorem min_difference_sum_k_equals_one
  {n k : Nat} {arr : List Int}
  (h1 : n = arr.length)
  (h2 : k = 1)
  (h3 : n > 1) :
  min_difference_sum n k arr = maximum arr - minimum arr :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval min_difference_sum 3 2 [1, 2, 4]

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_difference_sum 5 2 [3, -5, 3, -5, 3]

/-
info: 3
-/
-- #guard_msgs in
-- #eval min_difference_sum 6 3 [4, 3, 4, 3, 2, 5]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: unguarded