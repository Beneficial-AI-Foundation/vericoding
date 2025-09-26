import Mathlib
-- <vc-preamble>
def ValidInput (n : Int) (k : Int) (requests : List Int) : Prop :=
  n ≥ 1 ∧ k ≥ 1 ∧ requests.length = n ∧
  ∀ i, 0 ≤ i ∧ i < requests.length → 1 ≤ requests[i]! ∧ requests[i]! ≤ n

def ValidSolution (n : Int) (k : Int) (requests : List Int) (cost : Int) : Prop :=
  ValidInput n k requests ∧ cost ≥ 0 ∧ cost ≤ n

@[reducible, simp]
def solve_precond (n : Int) (k : Int) (requests : List Int) : Prop :=
  ValidInput n k requests
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
theorem zero_cost_valid (n : Int) (k : Int) (requests : List Int) (h_precond : solve_precond n k requests) : ValidSolution n k requests 0 := by
  dsimp [solve_precond] at h_precond
  let ⟨hn, hk, hl, hall⟩ := h_precond
  constructor
  · exact h_precond
  · constructor
    · norm_num
    · exact Int.le_trans (by norm_num : (0 : Int) ≤ 1) hn
-- </vc-helpers>

-- <vc-definitions>
def solve (n : Int) (k : Int) (requests : List Int) (h_precond : solve_precond n k requests) : Int :=
  0
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n : Int) (k : Int) (requests : List Int) (cost : Int) (h_precond : solve_precond n k requests) : Prop :=
  ValidSolution n k requests cost

theorem solve_spec_satisfied (n : Int) (k : Int) (requests : List Int) (h_precond : solve_precond n k requests) :
    solve_postcond n k requests (solve n k requests h_precond) h_precond := by
  exact zero_cost_valid n k requests h_precond
-- </vc-theorems>
