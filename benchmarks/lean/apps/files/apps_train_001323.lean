-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_wolverine_mutations (n k : Nat) (characteristics : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem wolverine_mutations_empty 
  (n k : Nat) (h1 : n ≥ 1) (h2 : k ≥ 1) :
  count_wolverine_mutations n k [] = 0 :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_wolverine_mutations 5 10 [2, 4, 1, 35, 1]

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_wolverine_mutations 3 5 [1, 2, 3]

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_wolverine_mutations 4 7 [7, 14, 21, 28]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible