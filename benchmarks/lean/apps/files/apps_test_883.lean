-- <vc-preamble>
def ValidInput (n : Int) (friends : List Int) : Prop :=
  n ≥ 1 ∧ friends.length = n ∧ ∀ i, 0 ≤ i ∧ i < friends.length → 1 ≤ friends[i]! ∧ friends[i]! ≤ 5

def sum_sequence (s : List Int) : Int :=
  match s with
  | [] => 0
  | x :: xs => x + sum_sequence xs

def DimaCleans (n : Int) (friends : List Int) (dima_fingers : Int) : Bool :=
  let total_sum := sum_sequence friends + dima_fingers
  let total_people := n + 1
  total_sum % total_people == 1

def CountValidChoicesHelper (n : Int) (friends : List Int) (finger_count : Int) : Int :=
  if finger_count == 1 then
    (if !DimaCleans n friends 1 then 1 else 0) +
    (if !DimaCleans n friends 2 then 1 else 0) +
    (if !DimaCleans n friends 3 then 1 else 0) +
    (if !DimaCleans n friends 4 then 1 else 0) +
    (if !DimaCleans n friends 5 then 1 else 0)
  else
    0

def CountValidChoices (n : Int) (friends : List Int) : Int :=
  CountValidChoicesHelper n friends 1

@[reducible, simp]
def solve_precond (n : Int) (friends : List Int) : Prop :=
  ValidInput n friends
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (friends : List Int) (h_precond : solve_precond n friends) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (friends : List Int) (result : Int) (h_precond : solve_precond n friends) : Prop :=
  0 ≤ result ∧ result ≤ 5 ∧ result = CountValidChoices n friends

theorem solve_spec_satisfied (n : Int) (friends : List Int) (h_precond : solve_precond n friends) :
    solve_postcond n friends (solve n friends h_precond) h_precond := by
  sorry
-- </vc-theorems>