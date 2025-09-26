import Mathlib
-- <vc-preamble>
def ValidInput (x y z : Int) : Prop :=
  x ≥ 1 ∧ y ≥ 1 ∧ z ≥ 1 ∧ y + 2 * z ≤ x

def MaxPeople (x y z : Int) (h : ValidInput x y z) : Int :=
  (x - z) / (y + z)

def ValidSolution (x y z : Int) (result : Int) (h : ValidInput x y z) : Prop :=
  result = MaxPeople x y z h ∧
  result ≥ 0 ∧
  result * (y + z) ≤ x - z ∧ x - z < (result + 1) * (y + z)

@[reducible, simp]
def solve_precond (x y z : Int) : Prop :=
  ValidInput x y z
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Lemma about integer division bounds
lemma int_div_bounds (a b : Int) (hb : b > 0) : a / b * b ≤ a ∧ a < (a / b + 1) * b := by
  constructor
  · exact Int.ediv_mul_le a (ne_of_gt hb)
  · exact Int.lt_ediv_add_one_mul_self a hb

-- LLM HELPER: Non-negativity of division result
lemma div_nonneg_of_valid (x y z : Int) (h : ValidInput x y z) : (x - z) / (y + z) ≥ 0 := by
  have h_pos : y + z > 0 := by
    have hy : y ≥ 1 := h.2.1
    have hz : z ≥ 1 := h.2.2.1
    linarith
  have h_nonneg : x - z ≥ 0 := by
    have hz : z ≥ 1 := h.2.2.1
    have h_bound : y + 2 * z ≤ x := h.2.2.2
    have : z ≤ 2 * z := by linarith
    linarith
  exact Int.ediv_nonneg h_nonneg (le_of_lt h_pos)
-- </vc-helpers>

-- <vc-definitions>
def solve (x y z : Int) (h_precond : solve_precond x y z) : Int :=
  MaxPeople x y z h_precond
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (x y z : Int) (result : Int) (h_precond : solve_precond x y z) : Prop :=
  ValidSolution x y z result h_precond

theorem solve_spec_satisfied (x y z : Int) (h_precond : solve_precond x y z) :
    solve_postcond x y z (solve x y z h_precond) h_precond := by
  unfold solve_postcond ValidSolution solve MaxPeople
  constructor
  · rfl
  constructor
  · exact div_nonneg_of_valid x y z h_precond
  constructor
  · have h_pos : y + z > 0 := by
      have hy : y ≥ 1 := h_precond.2.1
      have hz : z ≥ 1 := h_precond.2.2.1
      linarith
    exact (int_div_bounds (x - z) (y + z) h_pos).1
  · have h_pos : y + z > 0 := by
      have hy : y ≥ 1 := h_precond.2.1  
      have hz : z ≥ 1 := h_precond.2.2.1
      linarith
    exact (int_div_bounds (x - z) (y + z) h_pos).2
-- </vc-theorems>
