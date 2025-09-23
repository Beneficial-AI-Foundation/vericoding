-- <vc-preamble>
partial def IntToString (n : Int) : String :=
  if n < 0 then "-" ++ IntToString (-n)
  else if n < 10 then String.singleton (Char.ofNat (n.natAbs + 48))
  else IntToString (n / 10) ++ IntToString (n % 10)

def ValidOutput (n : Int) (result : List String) : Prop :=
  if n < 6 then
    result.length = 1 + (n - 1).natAbs ∧
    result[0]! = "-1" ∧
    (∀ i, 1 ≤ i ∧ i < result.length → result[i]! = "1 " ++ IntToString (i + 1))
  else
    result.length = (5 + (n - 6).natAbs) + (n - 1).natAbs ∧
    result[0]! = "1 2" ∧ result[1]! = "1 3" ∧ result[2]! = "1 4" ∧
    result[3]! = "2 5" ∧ result[4]! = "2 6" ∧
    (∀ i, 5 ≤ i ∧ i < 5 + (n - 6).natAbs → result[i]! = "1 " ++ IntToString (i + 2)) ∧
    (∀ i, 5 + (n - 6).natAbs ≤ i ∧ i < result.length → result[i]! = "1 " ++ IntToString (i - (5 + (n - 6).natAbs) + 2))

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  n ≥ 2
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (h_precond : solve_precond n) : List String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (result : List String) (h_precond : solve_precond n) : Prop :=
  ValidOutput n result

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  sorry
-- </vc-theorems>