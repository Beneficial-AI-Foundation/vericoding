-- <vc-preamble>
def f (n x : Int) : Int :=
  let y := n / x
  y + x * y * (y - 1) / 2

def IsDivisor (d n : Int) : Prop :=
  d > 0 ∧ n % d = 0

def IsSorted (s : List Int) : Prop :=
  ∀ i j, 0 ≤ i ∧ i < j ∧ j < s.length → s[i]! ≤ s[j]!

def NoDuplicates (s : List Int) : Prop :=
  ∀ i j, 0 ≤ i ∧ i < j ∧ j < s.length → s[i]! ≠ s[j]!

@[reducible, simp]
def solve_precond (n : Int) : Prop :=
  n ≥ 2
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
  NoDuplicates result ∧ 
  IsSorted result ∧ 
  (∀ v, v ∈ result ↔ ∃ d, IsDivisor d n ∧ v = f n d) ∧ 
  result.length > 0

theorem solve_spec_satisfied (n : Int) (h_precond : solve_precond n) :
    solve_postcond n (solve n h_precond) h_precond := by
  sorry
-- </vc-theorems>