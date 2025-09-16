-- <vc-preamble>
def ValidInput (n m k : Int) (emotes : List Int) : Prop :=
  n ≥ 2 ∧ k ≥ 1 ∧ m ≥ 1 ∧ emotes.length = n ∧
  ∀ i, 0 ≤ i ∧ i < emotes.length → emotes[i]! ≥ 1

def MaxValue (s : List Int) : Int :=
  sorry

def SecondMaxValue (s : List Int) : Int :=
  sorry

def FilterOut (s : List Int) (val : Int) (count : Int) : List Int :=
  sorry

def MaxHappiness (n m k : Int) (emotes : List Int) : Int :=
  let k_plus_1 := k + 1
  let total := m / k_plus_1
  let remainder := m % k_plus_1
  let max_val := MaxValue emotes
  let second_max_val := SecondMaxValue emotes
  remainder * max_val + max_val * (total * k) + second_max_val * total

@[reducible, simp]
def solve_precond (n m k : Int) (emotes : List Int) : Prop :=
  ValidInput n m k emotes
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n m k : Int) (emotes : List Int) (h_precond : solve_precond n m k emotes) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m k : Int) (emotes : List Int) (result : Int) (h_precond : solve_precond n m k emotes) : Prop :=
  result ≥ 0

theorem solve_spec_satisfied (n m k : Int) (emotes : List Int) (h_precond : solve_precond n m k emotes) :
    solve_postcond n m k emotes (solve n m k emotes h_precond) h_precond := by
  sorry
-- </vc-theorems>
