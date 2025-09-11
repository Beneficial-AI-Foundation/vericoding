-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MOD : Nat := 1000000007

def calculate_arrangements (n m : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calculate_arrangements_mod_bounds
  (n m : Int) (hn : n > 0) (hm : m > 0) :
  0 ≤ calculate_arrangements n m ∧ calculate_arrangements n m < MOD :=
  sorry

theorem calculate_arrangements_one_n
  (m : Int) (hm : m > 0) :
  calculate_arrangements 1 m = 1 :=
  sorry

theorem calculate_arrangements_nonNeg_invalid_n
  (n m : Int) (hn : n ≤ 0) (hm : m > 0) :
  calculate_arrangements n m ≥ 0 :=
  sorry

theorem calculate_arrangements_nonNeg_invalid_m
  (n m : Int) (hn : n > 0) (hm : m ≤ 0) :
  calculate_arrangements n m ≥ 0 :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval calculate_arrangements 1 10

/-
info: 64
-/
-- #guard_msgs in
-- #eval calculate_arrangements 5 2

/-
info: 729
-/
-- #guard_msgs in
-- #eval calculate_arrangements 4 3
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded