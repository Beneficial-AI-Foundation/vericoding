-- <vc-preamble>
def MOD := 1000000007

def calculate_offense_ways (n : Nat) (numbers : List Nat) : Nat :=
sorry

def isSorted (l : List Nat) : Bool :=
sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def natLeBool (a b : Nat) : Bool :=
  if a ≤ b then true else false
-- </vc-definitions>

-- <vc-theorems>
theorem result_range {n : Nat} {numbers : List Nat} :
  let result := calculate_offense_ways n numbers
  0 ≤ result ∧ result < MOD :=
sorry

theorem single_number {x : Nat} :
  x > 0 →
  calculate_offense_ways 1 [x] = x :=
sorry

theorem impossible_combinations_zero : 
  calculate_offense_ways 2 [1, 1] = 0 ∧
  calculate_offense_ways 3 [2, 2, 2] = 0 :=
sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval calculate_offense_ways 1 [4]

/-
info: 45
-/
-- #guard_msgs in
-- #eval calculate_offense_ways 2 [10, 5]

/-
info: 0
-/
-- #guard_msgs in
-- #eval calculate_offense_ways 4 [2, 3, 1, 3]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible