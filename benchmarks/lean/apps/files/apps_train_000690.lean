-- <vc-preamble>
def solve (n : Nat) (arr : List Nat) : Nat := 
  sorry

def find_max_gcd (arr : List Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def gcd_of_list (numbers : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_returns_valid : ∀ (n : Nat) (arr : List Nat),
  arr ≠ [] → solve n arr = arr.head! ∨ solve n arr = arr.getLast! :=
sorry

theorem solve_optimality : ∀ (n : Nat) (arr : List Nat),
  arr ≠ [] → 
  (arr.length = 1 → solve n arr = arr.head!) ∧
  (arr.length > 1 → solve n arr ≥ arr.head! ∧ solve n arr ≥ arr.getLast!) :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve 1 [2]

/-
info: 6
-/
-- #guard_msgs in
-- #eval solve 3 [6, 9, 3]

/-
info: 36
-/
-- #guard_msgs in
-- #eval solve 4 [12, 18, 24, 36]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible