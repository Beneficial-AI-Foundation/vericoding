-- <vc-preamble>
def IsStrongestInSchool (student_idx: Nat) (powers: List Int) (schools: List Int) : Prop :=
  student_idx < powers.length ∧ powers.length = schools.length ∧
  ∀ j, j < powers.length ∧ schools[j]! = schools[student_idx]! → powers[j]! ≤ powers[student_idx]!

def decidableIsStrongestInSchool (student_idx: Nat) (powers: List Int) (schools: List Int) : Bool :=
  if h : student_idx < powers.length ∧ powers.length = schools.length then
    (List.range powers.length).all (fun j => 
      if schools[j]! = schools[student_idx]! then powers[j]! ≤ powers[student_idx]! else true)
  else
    false

@[reducible, simp]
def solve_precond (n m k : Nat) (powers schools chosen : List Int) : Prop :=
  n ≥ 1 ∧ m ≥ 1 ∧ k ≥ 1 ∧ k ≤ n ∧ m ≤ n ∧
  powers.length = n ∧ schools.length = n ∧ chosen.length = k ∧
  (∀ i, i < n → 1 ≤ schools[i]! ∧ schools[i]! ≤ m) ∧
  (∀ i, i < k → 1 ≤ chosen[i]! ∧ chosen[i]! ≤ n) ∧
  (∀ i j, i < k ∧ j < k ∧ i ≠ j → chosen[i]! ≠ chosen[j]!) ∧
  (∀ i j, i < n ∧ j < n ∧ i ≠ j → powers[i]! ≠ powers[j]!) ∧
  (∀ s, 1 ≤ s ∧ s ≤ m → ∃ i, i < n ∧ schools[i]! = s) ∧
  (∀ i, i < n → 1 ≤ powers[i]! ∧ powers[i]! ≤ n)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n m k : Nat) (powers schools chosen : List Int) (h_precond : solve_precond n m k powers schools chosen) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m k : Nat) (powers schools chosen : List Int) (result: Nat) (h_precond : solve_precond n m k powers schools chosen) : Prop :=
  result ≤ k ∧
  result = (List.range k |>.filter (fun i => ¬decidableIsStrongestInSchool (Int.natAbs (chosen[i]! - 1)) powers schools)).length

theorem solve_spec_satisfied (n m k : Nat) (powers schools chosen : List Int) (h_precond : solve_precond n m k powers schools chosen) :
    solve_postcond n m k powers schools chosen (solve n m k powers schools chosen h_precond) h_precond := by
  sorry
-- </vc-theorems>