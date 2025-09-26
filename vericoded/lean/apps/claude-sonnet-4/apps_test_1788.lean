import Mathlib
-- <vc-preamble>
def ValidInput (a b : Int) : Prop :=
  -100 ≤ a ∧ a ≤ 100 ∧ -100 ≤ b ∧ b ≤ 100 ∧ (a + b) % 2 = 0 ∧ (a - b) % 2 = 0

def CorrectSolution (a b x y : Int) : Prop :=
  a = x + y ∧ b = x - y

@[reducible, simp]
def solve_precond (a b : Int) : Prop :=
  ValidInput a b
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Lemma showing that if n % 2 = 0, then 2 * (n / 2) = n
lemma div_two_mul_two_of_even (n : Int) (h : n % 2 = 0) : 2 * (n / 2) = n := by
  have h_dvd : 2 ∣ n := Int.dvd_iff_emod_eq_zero.mpr h
  exact Int.mul_ediv_cancel' h_dvd
-- </vc-helpers>

-- <vc-definitions>
def solve (a b : Int) (h_precond : solve_precond a b) : Int × Int :=
  ((a + b) / 2, (a - b) / 2)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b : Int) (result : Int × Int) (h_precond : solve_precond a b) : Prop :=
  CorrectSolution a b result.1 result.2

theorem solve_spec_satisfied (a b : Int) (h_precond : solve_precond a b) :
    solve_postcond a b (solve a b h_precond) h_precond := by
  -- Extract the parity conditions from the precondition
  have h_valid : ValidInput a b := h_precond
  have h_sum_even : (a + b) % 2 = 0 := h_valid.2.2.2.2.1
  have h_diff_even : (a - b) % 2 = 0 := h_valid.2.2.2.2.2
  -- Show that our solution satisfies the correctness conditions
  unfold solve_postcond CorrectSolution
  simp only [solve]
  constructor
  · -- Prove a = x + y where x = (a + b) / 2 and y = (a - b) / 2
    have h1 : 2 * ((a + b) / 2) = a + b := div_two_mul_two_of_even (a + b) h_sum_even
    have h2 : 2 * ((a - b) / 2) = a - b := div_two_mul_two_of_even (a - b) h_diff_even
    linarith
  · -- Prove b = x - y where x = (a + b) / 2 and y = (a - b) / 2
    have h1 : 2 * ((a + b) / 2) = a + b := div_two_mul_two_of_even (a + b) h_sum_even
    have h2 : 2 * ((a - b) / 2) = a - b := div_two_mul_two_of_even (a - b) h_diff_even
    linarith
-- </vc-theorems>
