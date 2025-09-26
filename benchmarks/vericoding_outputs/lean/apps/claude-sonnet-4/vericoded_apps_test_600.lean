import Mathlib
-- <vc-preamble>
def ValidInput (a b : Int) : Prop :=
  a ≥ 1 ∧ a ≤ 1000 ∧ b ≥ 1 ∧ b ≤ 1000 ∧ a ≠ b

def OptimalMeetingPoint (a b : Int) : Int :=
  (a + b) / 2

def tirednessForSteps (steps : Int) : Int :=
  if steps ≤ 0 then 0 else steps * (steps + 1) / 2

def MinimumTotalTiredness (a b : Int) (h : ValidInput a b) : Int :=
  let c := OptimalMeetingPoint a b
  tirednessForSteps (Int.natAbs (c - a)) + tirednessForSteps (Int.natAbs (b - c))

@[reducible, simp]
def solve_precond (a b : Int) : Prop :=
  ValidInput a b
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Prove that tiredness is always non-negative
lemma tirednessForSteps_nonneg (steps : Int) : tirednessForSteps steps ≥ 0 := by
  unfold tirednessForSteps
  split_ifs with h
  · simp
  · have h_pos : steps > 0 := Int.not_le.mp h
    have h_steps_nonneg : steps ≥ 0 := le_of_lt h_pos
    have h_steps_plus_one_pos : steps + 1 > 0 := Int.add_pos_of_nonneg_of_pos h_steps_nonneg (by norm_num)
    apply Int.ediv_nonneg
    · apply Int.mul_nonneg h_steps_nonneg
      exact le_of_lt h_steps_plus_one_pos
    · norm_num

-- LLM HELPER: Prove that minimum total tiredness is non-negative
lemma MinimumTotalTiredness_nonneg (a b : Int) (h : ValidInput a b) : 
    MinimumTotalTiredness a b h ≥ 0 := by
  unfold MinimumTotalTiredness
  apply Int.add_nonneg
  · exact tirednessForSteps_nonneg _
  · exact tirednessForSteps_nonneg _
-- </vc-helpers>

-- <vc-definitions>
def solve (a b : Int) (h_precond : solve_precond a b) : Int :=
  MinimumTotalTiredness a b h_precond
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b : Int) (result : Int) (h_precond : solve_precond a b) : Prop :=
  result ≥ 0 ∧ result = MinimumTotalTiredness a b h_precond

theorem solve_spec_satisfied (a b : Int) (h_precond : solve_precond a b) :
    solve_postcond a b (solve a b h_precond) h_precond := by
  unfold solve_postcond solve
  constructor
  · exact MinimumTotalTiredness_nonneg a b h_precond
  · rfl
-- </vc-theorems>
