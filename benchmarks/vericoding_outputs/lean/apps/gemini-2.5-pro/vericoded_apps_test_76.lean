import Mathlib
-- <vc-preamble>
def ValidInput (n m a b : Int) : Prop :=
  n ≥ 1 ∧ m ≥ 1 ∧ a ≥ 1 ∧ b ≥ 1

def MinCostToDivisible (n m a b : Int) : Int :=
  let k := n % m
  if k * b < (m - k) * a then k * b else (m - k) * a

@[reducible, simp]
def solve_precond (n m a b : Int) : Prop :=
  ValidInput n m a b
-- </vc-preamble>

-- <vc-helpers>

-- LLM HELPER
theorem MinCostToDivisible_nonneg (n m a b : Int) (h : ValidInput n m a b) :
  MinCostToDivisible n m a b ≥ 0 := by
  unfold MinCostToDivisible ValidInput at *
  rcases h with ⟨_, h_m, h_a, h_b⟩
  dsimp
  let k := n % m
  have hm_pos : m > 0 := by linarith
  have k_nonneg : k ≥ 0 := Int.emod_nonneg n (by linarith)
  split_ifs
  · apply mul_nonneg k_nonneg (by linarith)
  · have h_mk_nonneg : m - k ≥ 0 := by linarith [Int.emod_lt_of_pos n hm_pos]
    apply mul_nonneg h_mk_nonneg (by linarith)

-- </vc-helpers>

-- <vc-definitions>
def solve (n m a b : Int) (h_precond : solve_precond n m a b) : Int :=
  MinCostToDivisible n m a b
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m a b : Int) (result : Int) (h_precond : solve_precond n m a b) : Prop :=
  result = MinCostToDivisible n m a b ∧ result ≥ 0

theorem solve_spec_satisfied (n m a b : Int) (h_precond : solve_precond n m a b) :
    solve_postcond n m a b (solve n m a b h_precond) h_precond := by
  unfold solve_postcond solve
  simp
  apply MinCostToDivisible_nonneg
  exact h_precond
-- </vc-theorems>
