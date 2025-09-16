-- <vc-preamble>
def sum_list : List Nat → Nat 
  | [] => 0
  | (h :: t) => h + sum_list t
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_damage (n : Nat) (items : List Nat) : Nat := sorry

theorem damage_non_negative {n : Nat} {items : List Nat} 
  (h : items.length > 0) :
  calculate_damage n items ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
/-
info: 6
-/
-- #guard_msgs in
-- #eval calculate_damage 5 [1, 2, 3, 4, 5]

/-
info: 12
-/
-- #guard_msgs in
-- #eval calculate_damage 3 [2, 4, 6]

/-
info: 0
-/
-- #guard_msgs in
-- #eval calculate_damage 4 [1, 3, 5, 7]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible