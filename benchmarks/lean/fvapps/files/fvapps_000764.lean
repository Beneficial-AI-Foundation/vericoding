-- <vc-preamble>
def Command := Nat × Nat

/- Given commands are valid if they are within matrix bounds n×m -/

def valid_commands : Nat → Nat → List Command → Bool
  | n, m, cmds => cmds.all fun c => c.1 ≤ n && c.2 ≤ m

/- Solve strange matrix takes dimensions n,m and list of commands, returns list of sums -/
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_strange_matrix (n m k : Nat) (cmds : List Command) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_column
  (n : Nat)
  (h : n > 0) :
  let result := solve_strange_matrix n 1 0 []
  -- All entries are 0 for single column
  ∀ i : Nat, i < n → result.get! i = 0 :=
sorry

theorem single_row
  (m : Nat)
  (h : m > 0) :
  let result := solve_strange_matrix 1 m 0 []
  -- Single row has length 1
  result.length = 1 ∧
  -- Result is m-1
  result.get! 0 = m - 1 :=
sorry
-- </vc-theorems>