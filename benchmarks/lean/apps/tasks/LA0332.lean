-- <vc-preamble>
def min (a : List Int) (h : a.length > 0) : Int :=
  match a with
  | [x] => x
  | x :: xs => 
    if h_xs : xs.length > 0 then
      let min_rest := min xs h_xs
      if x ≤ min_rest then x else min_rest
    else x

@[reducible, simp]
def solve_precond (a : List Int) : Prop :=
  a.length > 0 ∧ ∀ i, 0 ≤ i ∧ i < a.length → a[i]! > 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a : List Int) (h_precond : solve_precond a) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a : List Int) (result : Int) (h_precond : solve_precond a) : Prop :=
  (result = -1 ∨ result ∈ a) ∧
  (result ≠ -1 → ∀ i, 0 ≤ i ∧ i < a.length → a[i]! % result = 0) ∧
  (result = -1 → ∀ x, x ∈ a → ∃ i, 0 ≤ i ∧ i < a.length ∧ a[i]! % x ≠ 0) ∧
  ((∀ i, 0 ≤ i ∧ i < a.length → a[i]! % (min a (by have := h_precond.1; exact this)) = 0) → 
   result = min a (by have := h_precond.1; exact this)) ∧
  ((∃ i, 0 ≤ i ∧ i < a.length ∧ a[i]! % (min a (by have := h_precond.1; exact this)) ≠ 0) → 
   result = -1)

theorem solve_spec_satisfied (a : List Int) (h_precond : solve_precond a) :
    solve_postcond a (solve a h_precond) h_precond := by
  sorry
-- </vc-theorems>