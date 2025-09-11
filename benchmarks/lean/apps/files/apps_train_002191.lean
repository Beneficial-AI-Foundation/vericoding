-- <vc-preamble>
def solve_good_substrings : String → Nat × Nat :=
  fun _ => sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverseString : String → String :=
  fun _ => sorry

#check solve_good_substrings
-- </vc-definitions>

-- <vc-theorems>
theorem solve_good_substrings_result_structure 
    {s : String} 
    (h : s.length > 0) :
    let result := solve_good_substrings s
    result.1 > 0 ∧ result.2 > 0 :=
  sorry

theorem solve_good_substrings_first_element_values
    {s : String}
    (h : s.length > 0) :
    let result := solve_good_substrings s
    result.1 = 1 ∨ result.1 = 2 ∨ result.1 = s.length :=
  sorry

theorem solve_good_substrings_count_bound
    {s : String}
    (h : s.length > 0) :
    let result := solve_good_substrings s
    result.2 ≤ s.length - 1 ∨ result.2 = 1 :=
  sorry

/-
info: (1, 1)
-/
-- #guard_msgs in
-- #eval solve_good_substrings "aab"

/-
info: (2, 3)
-/
-- #guard_msgs in
-- #eval solve_good_substrings "bcbc"

/-
info: (3, 1)
-/
-- #guard_msgs in
-- #eval solve_good_substrings "ddd"
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible