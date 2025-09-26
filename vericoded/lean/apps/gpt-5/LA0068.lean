import Mathlib
-- <vc-preamble>
def ValidInput (n : Nat) (m : Nat) (benches : List Nat) : Prop :=
  n > 0 ∧ m > 0 ∧ benches.length = n ∧ ∀ i, 0 ≤ i ∧ i < n → benches[i]! > 0

def max_seq (s : List Nat) : Nat :=
  if s.length = 0 then 0
  else s.foldl max 0

def sum_seq (s : List Nat) : Nat :=
  s.sum

@[reducible, simp]
def solve_precond (n : Nat) (m : Nat) (benches : List Nat) : Prop :=
  ValidInput n m benches
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma max_seq_nil : max_seq ([] : List Nat) = 0 := by
  simp [max_seq]

@[simp] lemma sum_seq_nil : sum_seq ([] : List Nat) = 0 := by
  simp [sum_seq]
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Nat) (m : Nat) (benches : List Nat) (h_precond : solve_precond n m benches) : Nat × Nat :=
  let current_max := max_seq benches
let total := sum_seq benches + m
let minimum := if total ≤ current_max * n then current_max else (total + n - 1) / n
let maximum := current_max + m
(minimum, maximum)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Nat) (m : Nat) (benches : List Nat) (result: Nat × Nat) (h_precond : solve_precond n m benches) : Prop :=
  let minimum := result.1
  let maximum := result.2
  let total := sum_seq benches + m
  let current_max := max_seq benches
  maximum = max_seq benches + m ∧
  (if total ≤ current_max * n then minimum = current_max
   else minimum = (total + n - 1) / n)

theorem solve_spec_satisfied (n : Nat) (m : Nat) (benches : List Nat) (h_precond : solve_precond n m benches) :
    solve_postcond n m benches (solve n m benches h_precond) h_precond := by
  by_cases hcond : sum_seq benches + m ≤ max_seq benches * n
  · simp [solve_postcond, solve, hcond]
  · simp [solve_postcond, solve, hcond]
-- </vc-theorems>
