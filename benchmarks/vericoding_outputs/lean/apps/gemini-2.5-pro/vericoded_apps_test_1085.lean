import Mathlib
-- <vc-preamble>
def ValidInput (n : Nat) : Prop :=
  n > 0

def reduce_by_divisor (n d : Nat) : Nat :=
  if n = 0 ∨ d ≤ 1 then n
  else if n % d = 0 ∧ n ≥ d then reduce_by_divisor (n / d) d else n
decreasing_by 
  simp_wf
  apply Nat.div_lt_self
  · omega
  · omega

def count_divisors (n : Nat) : Nat :=
  (List.range (n + 1)).filter (fun d => 1 ≤ d ∧ d ≤ n ∧ n % d = 0) |>.length

def count_special_divisors (n : Nat) : Nat :=
  (List.range (n + 1)).filter (fun d => 2 ≤ d ∧ d ≤ n ∧ n % d = 0 ∧ (reduce_by_divisor n d - 1) % d = 0) |>.length

def count_valid_k_values (n : Nat) : Int :=
  if n = 1 then -1
  else 
    (count_divisors (n - 1) : Int) + (count_special_divisors n : Int) - 1

@[reducible, simp]
def solve_precond (n : Nat) : Prop :=
  ValidInput n
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
/--
This theorem proves that `count_valid_k_values` always returns a value greater than or equal to -1.
This is a key part of the postcondition for `solve`.
-/
theorem count_valid_k_values_ge_neg_one (n : Nat) :
    (count_valid_k_values n : Int) ≥ -1 := by
  unfold count_valid_k_values
  split_ifs
  ·-- Case n = 1: result is -1, which is ≥ -1.
    decide
  · -- Case n ≠ 1: result is a sum of counts minus 1.
    -- The counts are non-negative, so their sum is non-negative.
    -- `linarith` can prove `a + b - 1 ≥ -1` from `a ≥ 0` and `b ≥ 0`.
    linarith [Int.natCast_nonneg (count_divisors (n - 1)), Int.natCast_nonneg (count_special_divisors n)]

-- </vc-helpers>

-- <vc-definitions>
def solve (n : Nat) (h_precond : solve_precond n) : Int :=
  count_valid_k_values n
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Nat) (result : Int) (h_precond : solve_precond n) : Prop :=
  result = count_valid_k_values n ∧
  (n = 1 → result = -1) ∧
  (n > 1 → result = (count_divisors (n - 1) : Int) + (count_special_divisors n : Int) - 1) ∧
  result ≥ -1

theorem solve_spec_satisfied (n : Nat) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
    -- Unfold the definitions of `solve` and `solve_postcond` to expose the proof goals.
  unfold solve solve_postcond
  -- The goal is a conjunction of four properties. We prove them one by one using `constructor`.
  constructor
  · -- 1. `result = count_valid_k_values n` which is `count_valid_k_values n = count_valid_k_values n`
    -- This is true by reflexivity.
    rfl
  · constructor
    · -- 2. `n = 1 → result = -1`
      -- We assume `n = 1` and prove the equality.
      intro h_n_eq_1
      -- `simp` uses the hypothesis `h_n_eq_1` to simplify the `if` in `count_valid_k_values`.
      simp [count_valid_k_values, h_n_eq_1]
    · constructor
      · -- 3. `n > 1 → result = ...`
        -- We assume `n > 1` and prove the equality.
        intro h_n_gt_1
        -- From `n > 1` we can deduce `n ≠ 1`, which is needed to simplify the `if`.
        have h_n_ne_1 : n ≠ 1 := by omega
        -- `simp` uses `h_n_ne_1` to simplify the `if` in `count_valid_k_values`.
        simp [count_valid_k_values, h_n_ne_1]
      · -- 4. `result ≥ -1`
        -- This is exactly what our helper theorem `count_valid_k_values_ge_neg_one` proves.
        exact count_valid_k_values_ge_neg_one n
-- </vc-theorems>
