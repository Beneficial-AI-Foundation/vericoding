-- <vc-preamble>
def ValidInput (n : Int) (s : String) : Prop :=
  n ≥ 1 ∧ s.length = n.natAbs

def count_adjacent_same_pairs_up_to (s : String) (i : Nat) : Nat :=
  if i ≤ 1 then 0
  else 
    let prev_char := if i - 1 < s.length then s.get (String.Pos.mk (i - 1)) else ' '
    let curr_char := if i ≥ 2 ∧ i - 2 < s.length then s.get (String.Pos.mk (i - 2)) else ' '
    (if prev_char = curr_char then 1 else 0) + count_adjacent_same_pairs_up_to s (i - 1)

def count_adjacent_same_pairs (s : String) (n : Int) : Int :=
  Int.ofNat (count_adjacent_same_pairs_up_to s n.natAbs)

@[reducible, simp]
def solve_precond (n : Int) (s : String) : Prop :=
  ValidInput n s
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (s : String) (h_precond : solve_precond n s) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (s : String) (result : Int) (h_precond : solve_precond n s) : Prop :=
  result ≥ 0 ∧ result ≤ n - 1 ∧ result = count_adjacent_same_pairs s n

theorem solve_spec_satisfied (n : Int) (s : String) (h_precond : solve_precond n s) :
    solve_postcond n s (solve n s h_precond) h_precond := by
  sorry
-- </vc-theorems>