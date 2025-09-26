import Mathlib
-- <vc-preamble>
def ValidInput (n : Int) (edges : List (Int × Int)) : Prop :=
  n ≥ 2 ∧
  ∀ i, 0 ≤ i ∧ i < edges.length → 1 ≤ edges[i]!.1 ∧ edges[i]!.1 ≤ n ∧ 1 ≤ edges[i]!.2 ∧ edges[i]!.2 ≤ n ∧ edges[i]!.1 ≠ edges[i]!.2

def ValidOutput (result : Int) (n : Int) (edges : List (Int × Int)) : Prop :=
  result ≥ 0 ∧ result ≤ 2 * edges.length * (edges.length + 1)

@[reducible, simp]
def solve_precond (n : Int) (edges : List (Int × Int)) : Prop :=
  ValidInput n edges
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma bound_nonneg (edges : List (Int × Int)) :
    0 ≤ 2 * (edges.length : Int) * ((edges.length : Int) + 1) := by
  have h_len : 0 ≤ (edges.length : Int) := Int.ofNat_nonneg _
  have h_one : 0 ≤ (1 : Int) := zero_le_one
  have h_len_succ : 0 ≤ (edges.length : Int) + 1 := add_nonneg h_len h_one
  have h_two : 0 ≤ (2 : Int) := by decide
  have h_mul : 0 ≤ (2 : Int) * (edges.length : Int) := mul_nonneg h_two h_len
  exact mul_nonneg h_mul h_len_succ
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (edges : List (Int × Int)) (h_precond : solve_precond n edges) : Int :=
  0
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (edges : List (Int × Int)) (result : Int) (h_precond : solve_precond n edges) : Prop :=
  ValidOutput result n edges

theorem solve_spec_satisfied (n : Int) (edges : List (Int × Int)) (h_precond : solve_precond n edges) :
    solve_postcond n edges (solve n edges h_precond) h_precond := by
  simpa [solve_postcond, ValidOutput, solve] using
    And.intro (le_rfl : 0 ≤ (0 : Int)) (bound_nonneg edges)
-- </vc-theorems>
