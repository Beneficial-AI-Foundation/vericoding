-- <vc-preamble>
def ValidInput (n m p : Int) (f g : List Int) : Prop :=
  n ≥ 1 ∧ m ≥ 1 ∧
  p ≥ 2 ∧
  f.length = n ∧ g.length = m ∧
  (∀ k, 0 ≤ k ∧ k < f.length → f[k]! > 0) ∧
  (∀ k, 0 ≤ k ∧ k < g.length → g[k]! > 0) ∧
  (∃ k, 0 ≤ k ∧ k < f.length ∧ f[k]! % p ≠ 0) ∧
  (∃ k, 0 ≤ k ∧ k < g.length ∧ g[k]! % p ≠ 0)

def ValidResult (result n m p : Int) (f g : List Int) : Prop :=
  ∃ i j, 0 ≤ i ∧ i < f.length ∧ 0 ≤ j ∧ j < g.length ∧
  (∀ k, 0 ≤ k ∧ k < i → f[k]! % p = 0) ∧
  f[i]! % p ≠ 0 ∧
  (∀ k, 0 ≤ k ∧ k < j → g[k]! % p = 0) ∧
  g[j]! % p ≠ 0 ∧
  result = i + j ∧
  0 ≤ result ∧ result < f.length + g.length

@[reducible, simp]
def solve_precond (n m p : Int) (f g : List Int) : Prop :=
  ValidInput n m p f g ∧ p ≠ 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n m p : Int) (f g : List Int) (h_precond : solve_precond n m p f g) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m p : Int) (f g : List Int) (result : Int) (h_precond : solve_precond n m p f g) : Prop :=
  ValidResult result n m p f g

theorem solve_spec_satisfied (n m p : Int) (f g : List Int) (h_precond : solve_precond n m p f g) :
    solve_postcond n m p f g (solve n m p f g h_precond) h_precond := by
  sorry
-- </vc-theorems>