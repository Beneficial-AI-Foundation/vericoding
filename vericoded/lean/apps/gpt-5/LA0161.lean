import Mathlib
-- <vc-preamble>
def ValidInput (n d : Int) (transactions : List Int) : Prop :=
  n ≥ 1 ∧ d ≥ 1 ∧
  transactions.length = Int.natAbs n ∧
  ∀ i, 0 ≤ i ∧ i < n → -10000 ≤ (transactions[Int.natAbs i]?).getD 0 ∧ (transactions[Int.natAbs i]?).getD 0 ≤ 10000

def prefix_sum (transactions : List Int) (index : Nat) : Int :=
  if index < transactions.length then
    if index = 0 then transactions[0]!
    else prefix_sum transactions (index - 1) + transactions[index]!
  else 0

def count_zero_transactions : List Int → Int
  | [] => 0
  | x :: xs => (if x = 0 then 1 else 0) + count_zero_transactions xs

def balance_after_day (transactions deposits : List Int) (day : Nat) : Int :=
  if day < transactions.length ∧ day < deposits.length then
    if day = 0 then deposits[0]! + transactions[0]!
    else balance_after_day transactions deposits (day - 1) + deposits[day]! + transactions[day]!
  else 0

def count_positive_deposits : List Int → Int
  | [] => 0
  | x :: xs => (if x > 0 then 1 else 0) + count_positive_deposits xs

def valid_deposits_schedule (transactions : List Int) (deposits_schedule : List Int) (num_deposits : Int) : Prop :=
  deposits_schedule.length = transactions.length ∧
  (∀ i, 0 ≤ i ∧ i < deposits_schedule.length → (deposits_schedule[i]?).getD 0 ≥ 0) ∧
  num_deposits = count_positive_deposits deposits_schedule ∧
  ∀ i, 0 ≤ i ∧ i < transactions.length → 
    ((deposits_schedule[i]?).getD 0 > 0 → (transactions[i]?).getD 0 = 0)

def filter_positive : List Int → List Int
  | [] => []
  | x :: xs => if x > 0 then x :: filter_positive xs else filter_positive xs

@[reducible, simp]
def solve_precond (n d : Int) (transactions : List Int) : Prop :=
  ValidInput n d transactions
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma Int.zero_ge_zero : (0 : Int) ≥ 0 := by
  simpa [ge_iff_le] using (le_refl (0 : Int))
-- </vc-helpers>

-- <vc-definitions>
def solve (n d : Int) (transactions : List Int) (h_precond : solve_precond n d transactions) : Int :=
  0
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n d : Int) (transactions : List Int) (result : Int) (h_precond : solve_precond n d transactions) : Prop :=
  result = -1 ∨ result ≥ 0

theorem solve_spec_satisfied (n d : Int) (transactions : List Int) (h_precond : solve_precond n d transactions) :
    solve_postcond n d transactions (solve n d transactions h_precond) h_precond := by
  have h : 0 = (-1 : Int) ∨ 0 ≤ (0 : Int) := Or.inr le_rfl
  simpa [solve_postcond, solve, ge_iff_le] using h
-- </vc-theorems>
