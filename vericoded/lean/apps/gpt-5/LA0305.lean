import Mathlib
-- <vc-preamble>
def ValidInput (n a b c t : Int) (arrivals : List Int) : Prop :=
  1 ≤ n ∧ n ≤ 1000 ∧
  1 ≤ a ∧ a ≤ 1000 ∧
  1 ≤ b ∧ b ≤ 1000 ∧
  1 ≤ c ∧ c ≤ 1000 ∧
  1 ≤ t ∧ t ≤ 1000 ∧
  arrivals.length = n ∧
  ∀ i, 0 ≤ i ∧ i < arrivals.length → 1 ≤ arrivals[i]! ∧ arrivals[i]! ≤ t

def sum_seq (s : List Int) : Int :=
  match s with
  | [] => 0
  | x :: xs => x + sum_seq xs

def MaxMoney (n a b c t : Int) (arrivals : List Int) (h : ValidInput n a b c t arrivals) : Int :=
  if b > c then n * a
  else n * a + (c - b) * (n * t - sum_seq arrivals)

@[reducible, simp]
def solve_precond (n a b c t : Int) (arrivals : List Int) : Prop :=
  ValidInput n a b c t arrivals
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma sum_seq_nil : sum_seq ([] : List Int) = 0 := rfl

-- LLM HELPER
@[simp] lemma sum_seq_cons (x : Int) (xs : List Int) : sum_seq (x :: xs) = x + sum_seq xs := rfl
-- </vc-helpers>

-- <vc-definitions>
def solve (n a b c t : Int) (arrivals : List Int) (h_precond : solve_precond n a b c t arrivals) : Int :=
  MaxMoney n a b c t arrivals h_precond
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n a b c t : Int) (arrivals : List Int) (result : Int) (h_precond : solve_precond n a b c t arrivals) : Prop :=
  result = MaxMoney n a b c t arrivals h_precond

theorem solve_spec_satisfied (n a b c t : Int) (arrivals : List Int) (h_precond : solve_precond n a b c t arrivals) :
    solve_postcond n a b c t arrivals (solve n a b c t arrivals h_precond) h_precond := by
  simp [solve_postcond, solve]
-- </vc-theorems>
