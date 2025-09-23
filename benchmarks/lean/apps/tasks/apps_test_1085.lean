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
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Nat) (h_precond : solve_precond n) : Int :=
  sorry
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
  sorry
-- </vc-theorems>