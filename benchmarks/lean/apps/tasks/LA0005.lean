-- <vc-preamble>
def ValidInput (n : Nat) (s : String) : Prop :=
  s.length = n

def CanCopyAt (s : String) (n : Nat) (i : Nat) : Bool :=
  let prefix_len := i + 1
  let end_pos := i + 1 + prefix_len
  decide (end_pos ≤ n) && decide (s.take prefix_len = (s.drop (i + 1)).take prefix_len)

def MaxCopySavingsUpTo (s : String) (n : Nat) (limit : Nat) : Nat :=
  if limit = 0 then 0
  else
    let i := limit - 1
    let current := if CanCopyAt s n i then i else 0
    let prev := MaxCopySavingsUpTo s n i
    if current > prev then current else prev

def MaxCopySavings (s : String) (n : Nat) : Nat :=
  MaxCopySavingsUpTo s n (n / 2)

@[reducible, simp]
def solve_precond (n : Nat) (s : String) : Prop :=
  ValidInput n s
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Nat) (s : String) (h_precond : solve_precond n s) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Nat) (s : String) (result : Nat) (h_precond : solve_precond n s) : Prop :=
  result ≤ n ∧ 
  (n = 0 → result = 0) ∧ 
  (n > 0 → result ≥ 1) ∧ 
  result = n - MaxCopySavings s n

theorem solve_spec_satisfied (n : Nat) (s : String) (h_precond : solve_precond n s) :
    solve_postcond n s (solve n s h_precond) h_precond := by
  sorry
-- </vc-theorems>