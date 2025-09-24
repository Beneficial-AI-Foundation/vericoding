-- <vc-preamble>
def ValidSolution (n a b c : Int) : Prop :=
  a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ 3 * a + 5 * b + 7 * c = n

def ValidResult (n : Int) (result : List Int) : Prop :=
  (result.length = 1 ∧ result[0]! = -1) ∨
  (result.length = 3 ∧ result[0]! ≥ 0 ∧ result[1]! ≥ 0 ∧ result[2]! ≥ 0 ∧ 
   ValidSolution n result[0]! result[1]! result[2]!)

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  n ≥ 1
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (h_precond : solve_precond n) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (result : List Int) (h_precond : solve_precond n) : Prop :=
  ValidResult n result ∧
  (n % 3 = 0 → result.length = 3 ∧ result = [n / 3, 0, 0]) ∧
  (n % 3 = 1 ∧ n < 7 → result.length = 1 ∧ result[0]! = -1) ∧
  (n % 3 = 1 ∧ n ≥ 7 → result.length = 3 ∧ result = [(n - 7) / 3, 0, 1]) ∧
  (n % 3 = 2 ∧ n < 5 → result.length = 1 ∧ result[0]! = -1) ∧
  (n % 3 = 2 ∧ n ≥ 5 → result.length = 3 ∧ result = [(n - 5) / 3, 1, 0])

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  sorry
-- </vc-theorems>