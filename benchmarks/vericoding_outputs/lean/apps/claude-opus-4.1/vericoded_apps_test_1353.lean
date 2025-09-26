import Mathlib
-- <vc-preamble>
def ValidInput (n m a b : Int) : Prop :=
  n ≥ 1 ∧ n ≤ 1000 ∧
  m ≥ 1 ∧ m ≤ 1000 ∧
  a ≥ 1 ∧ a ≤ 1000 ∧
  b ≥ 1 ∧ b ≤ 1000

def OptimalCost (n m a b : Int) (h : ValidInput n m a b) : Int :=
  min (n * a) (min (((n + m - 1) / m) * b) ((n / m) * b + (n % m) * a))

@[reducible, simp]
def solve_precond (n m a b : Int) : Prop :=
  ValidInput n m a b
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma min_nonneg (x y : Int) (hx : x ≥ 0) (hy : y ≥ 0) : min x y ≥ 0 := by
  simp [min_def]
  split
  · exact hx
  · exact hy

-- LLM HELPER
lemma cost_nonneg (n m a b : Int) (h : ValidInput n m a b) : OptimalCost n m a b h ≥ 0 := by
  unfold OptimalCost
  apply min_nonneg
  · -- n * a ≥ 0
    apply Int.mul_nonneg
    · have : n ≥ 1 := h.1
      omega
    · have : a ≥ 1 := h.2.2.2.2.1
      omega
  apply min_nonneg
  · -- ((n + m - 1) / m) * b ≥ 0
    apply Int.mul_nonneg
    · apply Int.ediv_nonneg
      · have hn : n ≥ 1 := h.1
        have hm : m ≥ 1 := h.2.2.1
        omega
      · have : m ≥ 1 := h.2.2.1
        omega
    · have : b ≥ 1 := h.2.2.2.2.2.2.1
      omega
  · -- (n / m) * b + (n % m) * a ≥ 0
    apply Int.add_nonneg
    · apply Int.mul_nonneg
      · apply Int.ediv_nonneg
        · have : n ≥ 1 := h.1
          omega
        · have : m ≥ 1 := h.2.2.1
          omega
      · have : b ≥ 1 := h.2.2.2.2.2.2.1
        omega
    · apply Int.mul_nonneg
      · apply Int.emod_nonneg
        intro hm
        have : m ≥ 1 := h.2.2.1
        omega
      · have : a ≥ 1 := h.2.2.2.2.1
        omega
-- </vc-helpers>

-- <vc-definitions>
def solve (n m a b : Int) (h_precond : solve_precond n m a b) : Int :=
  min (n * a) (min (((n + m - 1) / m) * b) ((n / m) * b + (n % m) * a))
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n m a b : Int) (result : Int) (h_precond : solve_precond n m a b) : Prop :=
  result ≥ 0 ∧ result = OptimalCost n m a b h_precond

theorem solve_spec_satisfied (n m a b : Int) (h_precond : solve_precond n m a b) :
    solve_postcond n m a b (solve n m a b h_precond) h_precond := by
  unfold solve_postcond solve
  simp [solve_precond] at h_precond
  constructor
  · exact cost_nonneg n m a b h_precond
  · rfl
-- </vc-theorems>
