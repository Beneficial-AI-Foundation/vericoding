-- <vc-preamble>
def maximum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | h::t => List.foldl max h t
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_max_group_strengths (n : Nat) (heights : List Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem length_matches_input 
  {n : Nat} {heights : List Nat} 
  (h1 : heights.length > 0) (h2 : heights.length = n) 
  (h3 : ∀ x ∈ heights, x > 0 ∧ x ≤ 10^9) :
  (find_max_group_strengths n heights).length = n :=
sorry

theorem monotonically_decreasing
  {n : Nat} {heights : List Nat}
  (h1 : heights.length > 0) (h2 : heights.length = n)
  (h3 : ∀ x ∈ heights, x > 0 ∧ x ≤ 10^9) :
  ∀ i, i + 1 < n → 
    (find_max_group_strengths n heights)[i]! ≥ (find_max_group_strengths n heights)[i+1]! :=
sorry

theorem first_value_is_max
  {n : Nat} {heights : List Nat}
  (h1 : heights.length > 0) (h2 : heights.length = n)
  (h3 : ∀ x ∈ heights, x > 0 ∧ x ≤ 10^9) :
  (find_max_group_strengths n heights)[0]! ≤ maximum heights :=
sorry

theorem preserves_input
  {n : Nat} {heights heights_copy : List Nat}
  (h1 : heights.length > 0) (h2 : heights.length = n)
  (h3 : heights = heights_copy)
  (h4 : ∀ x ∈ heights, x > 0) :
  let _ := find_max_group_strengths n heights_copy
  heights = heights_copy :=
sorry

theorem last_value_positive
  {n : Nat} {heights : List Nat}
  (h1 : heights.length > 0) (h2 : heights.length = n)
  (h3 : ∀ x ∈ heights, x > 0 ∧ x ≤ 10^9) :
  (find_max_group_strengths n heights)[heights.length - 1]! > 0 :=
sorry

/-
info: [6, 4, 4, 3, 3, 2, 2, 1, 1, 1]
-/
-- #guard_msgs in
-- #eval find_max_group_strengths 10 heights1.copy()

/-
info: [923264237, 524125987, 374288891]
-/
-- #guard_msgs in
-- #eval find_max_group_strengths 3 heights2.copy()

/-
info: [585325539, 365329221, 365329221, 291882089, 291882089]
-/
-- #guard_msgs in
-- #eval find_max_group_strengths 5 heights3.copy()
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: unguarded