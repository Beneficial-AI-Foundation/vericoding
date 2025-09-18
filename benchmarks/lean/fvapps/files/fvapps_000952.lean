-- <vc-preamble>
def min_horse_skill_diff (n : Nat) (skills : List Nat) : Nat :=
sorry

def list_max (l : List Nat) : Nat :=
sorry

def list_min (l : List Nat) : Nat :=
sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def list_sort (l : List Nat) : List Nat :=
sorry

-- Result is non-negative
-- </vc-definitions>

-- <vc-theorems>
theorem min_horse_skill_diff_nonneg {n : Nat} {skills : List Nat} 
  (h : skills.length = n) (h2 : skills.length ≥ 2) :
  min_horse_skill_diff n skills ≥ 0 :=
sorry

-- Result is at most the range of skills

theorem min_horse_skill_diff_le_range {n : Nat} {skills : List Nat}
  (h : skills.length = n) (h2 : skills.length ≥ 2) :
  min_horse_skill_diff n skills ≤ list_max skills - list_min skills :=
sorry

-- Result is at most any adjacent difference in sorted elements

theorem min_horse_skill_diff_le_adjacent {n : Nat} {skills : List Nat} {i : Nat}
  (h : skills.length = n) (h2 : skills.length ≥ 2) (h3 : i < skills.length - 1) :
  min_horse_skill_diff n skills ≤ 
    (list_sort skills).get! (i+1) - (list_sort skills).get! i :=
sorry

-- Result is invariant under list reordering

theorem min_horse_skill_diff_order_inv {n : Nat} {skills shuffled : List Nat}
  (h : skills.length = n) (h2 : skills.length ≥ 2)
  (h3 : list_sort skills = list_sort shuffled) :
  min_horse_skill_diff n skills = min_horse_skill_diff n shuffled :=
sorry

-- n must match list length

theorem min_horse_skill_diff_invalid {n : Nat} {skills : List Nat} 
  (h : skills.length ≠ n) :
  min_horse_skill_diff n skills = 0 :=
sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval min_horse_skill_diff 5 [4, 9, 1, 32, 13]

/-
info: 1
-/
-- #guard_msgs in
-- #eval min_horse_skill_diff 3 [4, 5, 6]

/-
info: 9
-/
-- #guard_msgs in
-- #eval min_horse_skill_diff 4 [1, 10, 100, 1000]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded