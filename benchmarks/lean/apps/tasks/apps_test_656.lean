-- <vc-preamble>
def count_negative_temp_days (temps : List Int) : Int :=
  match temps with
  | [] => 0
  | t :: ts => (if t < 0 then 1 else 0) + count_negative_temp_days ts

@[reducible, simp]
def solve_precond (n k : Int) (temps : List Int) : Prop :=
  n ≥ 1 ∧ k ≥ 0 ∧ k ≤ n ∧ temps.length = n ∧ ∀ i : Nat, 0 ≤ i ∧ i < n → -20 ≤ temps[i]! ∧ temps[i]! ≤ 20
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (n k : Int) (temps : List Int) (h_precond : solve_precond n k temps) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n k : Int) (temps : List Int) (result : Int) (h_precond : solve_precond n k temps) : Prop :=
  (result = -1 ↔ count_negative_temp_days temps > k) ∧
  (result ≠ -1 → result ≥ 0) ∧
  (result = 0 → ∀ i : Nat, 0 ≤ i ∧ i < n → temps[i]! ≥ 0) ∧
  (result > 0 → ∃ i : Nat, 0 ≤ i ∧ i < n ∧ temps[i]! < 0)

theorem solve_spec_satisfied (n k : Int) (temps : List Int) (h_precond : solve_precond n k temps) :
    solve_postcond n k temps (solve n k temps h_precond) h_precond := by
  sorry
-- </vc-theorems>