import Mathlib
-- <vc-preamble>
def validInput (a b c d : Int) : Prop :=
  0 ≤ a ∧ a < b ∧ b ≤ 100 ∧ 0 ≤ c ∧ c < d ∧ d ≤ 100

def myMin (x y : Int) : Int :=
  if x < y then x else y

def myMax (x y : Int) : Int :=
  if x > y then x else y

def intervalOverlapLength (a b c d : Int) : Int :=
  if myMin b d - myMax a c > 0 then myMin b d - myMax a c else 0

@[reducible, simp]
def solve_precond (a b c d : Int) : Prop :=
  validInput a b c d
-- </vc-preamble>

-- <vc-helpers>
 -- LLM HELPER
theorem intervalOverlapLength_nonneg (a b c d : Int) :
    intervalOverlapLength a b c d ≥ 0 := by
  unfold intervalOverlapLength
  split_ifs
  · linarith
  · rfl

-- LLM HELPER
theorem intervalOverlapLength_le_100 (h_precond : solve_precond a b c d) :
    intervalOverlapLength a b c d ≤ 100 := by
  rcases h_precond with ⟨ha_ge_0, _, hb_le_100, hc_ge_0, _, hd_le_100⟩
  simp only [intervalOverlapLength, myMin, myMax]
  split_ifs <;> linarith

-- </vc-helpers>

-- <vc-definitions>
def solve (a b c d : Int) (h_precond : solve_precond a b c d) : Int :=
  intervalOverlapLength a b c d
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (a b c d : Int) (result: Int) (h_precond : solve_precond a b c d) : Prop :=
  result ≥ 0 ∧ result = intervalOverlapLength a b c d ∧ result ≤ 100

theorem solve_spec_satisfied (a b c d : Int) (h_precond : solve_precond a b c d) :
    solve_postcond a b c d (solve a b c d h_precond) h_precond := by
  
  unfold solve_postcond solve
  constructor
  · exact intervalOverlapLength_nonneg a b c d
  · constructor
    · rfl
    · exact intervalOverlapLength_le_100 h_precond

-- </vc-theorems>
