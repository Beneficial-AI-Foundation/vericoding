-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def array_leaders (numbers : List Int) : List Int := sorry

def sumList : List Int → Int
  | [] => 0
  | x :: xs => x + sumList xs
-- </vc-definitions>

-- <vc-theorems>
theorem array_leaders_result_is_subset
  (numbers : List Int) :
  ∀ x ∈ array_leaders numbers, x ∈ numbers := sorry

theorem non_leaders_sum_property
  (numbers : List Int) 
  (i : Nat)
  (h1 : i < numbers.length)
  (h2 : numbers.get ⟨i, h1⟩ ∉ array_leaders numbers) :
  numbers.get ⟨i, h1⟩ ≤ sumList (numbers.drop (i+1)) := sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval array_leaders [1, 2, 3, 4, 0]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval array_leaders [16, 17, 4, 3, 5, 2]

/-
info: expected3
-/
-- #guard_msgs in
-- #eval array_leaders [0, -1, -29, 3, 2]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded