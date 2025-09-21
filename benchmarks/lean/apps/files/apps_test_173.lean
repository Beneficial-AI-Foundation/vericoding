-- <vc-preamble>
def ValidInput (n m : Int) (horizontal vertical : List Char) : Prop :=
  n ≥ 2 ∧ n ≤ 20 ∧ m ≥ 2 ∧ m ≤ 20 ∧
  horizontal.length = n ∧ vertical.length = m ∧
  (∀ c ∈ horizontal, c = '<' ∨ c = '>') ∧
  (∀ c ∈ vertical, c = '^' ∨ c = 'v')

def IsDisconnected (hor ver : List Char) : Prop :=
  (hor.length > 0 ∧ ver.length > 0 ∧ hor[0]! = '>' ∧ ver[0]! = 'v') ∨
  (hor.length > 0 ∧ ver.length > 0 ∧ hor[0]! = '<' ∧ ver[ver.length-1]! = 'v') ∨
  (hor.length > 0 ∧ ver.length > 0 ∧ hor[hor.length-1]! = '>' ∧ ver[0]! = '^') ∨
  (hor.length > 0 ∧ ver.length > 0 ∧ hor[hor.length-1]! = '<' ∧ ver[ver.length-1]! = '^')

axiom split (s : List Char) (delimiter : Char) : List (List Char)

axiom is_integer (s : List Char) : Bool

axiom parse_int (s : List Char) : Int

@[reducible, simp]
def solve_precond (n m : Int) (horizontal vertical : List Char) : Prop :=
  ValidInput n m horizontal vertical
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n m : Int) (horizontal vertical : List Char) (h_precond : solve_precond n m horizontal vertical) : List Char :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m : Int) (horizontal vertical : List Char) (result : List Char) (h_precond : solve_precond n m horizontal vertical) : Prop :=
  (result = "YES\n".toList ∨ result = "NO\n".toList) ∧
  (result = "NO\n".toList ↔ IsDisconnected horizontal vertical)

theorem solve_spec_satisfied (n m : Int) (horizontal vertical : List Char) (h_precond : solve_precond n m horizontal vertical) :
    solve_postcond n m horizontal vertical (solve n m horizontal vertical h_precond) h_precond := by
  sorry
-- </vc-theorems>