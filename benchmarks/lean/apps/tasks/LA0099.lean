-- <vc-preamble>
def pos1 (a b c : Int) : Int :=
  if a ≤ b ∧ a ≤ c then a
  else if b ≤ a ∧ b ≤ c then b
  else c

def pos2 (a b c : Int) : Int :=
  if a ≤ b ∧ a ≤ c then
    if b ≤ c then b else c
  else if b ≤ a ∧ b ≤ c then
    if a ≤ c then a else c
  else
    if a ≤ b then a else b

def pos3 (a b c : Int) : Int :=
  if a ≤ b ∧ a ≤ c then
    if b ≤ c then c else b
  else if b ≤ a ∧ b ≤ c then
    if a ≤ c then c else a
  else
    if a ≤ b then b else a

@[reducible, simp]
def solve_precond (a b c d : Int) : Prop :=
  1 ≤ a ∧ a ≤ 1000000000 ∧
  1 ≤ b ∧ b ≤ 1000000000 ∧
  1 ≤ c ∧ c ≤ 1000000000 ∧
  1 ≤ d ∧ d ≤ 1000000000
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a b c d : Int) (h_precond : solve_precond a b c d) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b c d : Int) (result: Int) (h_precond : solve_precond a b c d) : Prop :=
  result ≥ 0 ∧
  result = (if d > (pos2 a b c - pos1 a b c) then d - (pos2 a b c - pos1 a b c) else 0) +
           (if d > (pos3 a b c - pos2 a b c) then d - (pos3 a b c - pos2 a b c) else 0)

theorem solve_spec_satisfied (a b c d : Int) (h_precond : solve_precond a b c d) :
    solve_postcond a b c d (solve a b c d h_precond) h_precond := by
  sorry
-- </vc-theorems>