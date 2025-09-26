import Mathlib
-- <vc-preamble>
@[reducible, simp]
def ValidPosition (pos : Int) : Prop :=
  0 ≤ pos ∧ pos ≤ 2

def SwapMove (pos : Int) (moveNum : Int) (h_valid : ValidPosition pos) (h_move : moveNum ≥ 1) : Int :=
  if moveNum % 2 = 1 then
    if pos = 0 then 1
    else if pos = 1 then 0
    else 2
  else
    if pos = 1 then 2
    else if pos = 2 then 1
    else 0

def ReverseMove (pos : Int) (moveNum : Int) (h_valid : ValidPosition pos) (h_move : moveNum ≥ 1) : Int :=
  if moveNum % 2 = 1 then
    if pos = 0 then 1
    else if pos = 1 then 0
    else 2
  else
    if pos = 1 then 2
    else if pos = 2 then 1
    else 0

@[reducible, simp]
def solve_precond (n x : Int) : Prop :=
  n ≥ 1 ∧ n ≤ 2000000000 ∧ ValidPosition x
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma valid_pos_is_0_1_2 (pos : Int) (h : ValidPosition pos) : pos = 0 ∨ pos = 1 ∨ pos = 2 := by
  rcases h with ⟨h_ge, h_le⟩
  interval_cases pos
  · left; rfl
  · right; left; rfl
  · right; right; rfl

-- LLM HELPER
def T1 (pos : Int) : Int := if pos = 0 then 1 else if pos = 1 then 0 else 2
-- LLM HELPER
def T2 (pos : Int) : Int := if pos = 0 then 2 else if pos = 1 then 0 else 1
-- LLM HELPER
def T3 (pos : Int) : Int := if pos = 0 then 2 else if pos = 2 then 0 else 1
-- LLM HELPER
def T4 (pos : Int) : Int := if pos = 0 then 1 else if pos = 1 then 2 else 0
-- LLM HELPER
def T5 (pos : Int) : Int := if pos = 1 then 2 else if pos = 2 then 1 else 0
-- LLM HELPER
def T6 (pos : Int) : Int := pos

-- LLM HELPER
lemma T1_valid (pos : Int) (h : ValidPosition pos) : ValidPosition (T1 pos) := by
  rcases valid_pos_is_0_1_2 pos h with rfl | rfl | rfl <;> simp [T1]
-- LLM HELPER
lemma T2_valid (pos : Int) (h : ValidPosition pos) : ValidPosition (T2 pos) := by
  rcases valid_pos_is_0_1_2 pos h with rfl | rfl | rfl <;> simp [T2]
-- LLM HELPER
lemma T3_valid (pos : Int) (h : ValidPosition pos) : ValidPosition (T3 pos) := by
  rcases valid_pos_is_0_1_2 pos h with rfl | rfl | rfl <;> simp [T3]
-- LLM HELPER
lemma T4_valid (pos : Int) (h : ValidPosition pos) : ValidPosition (T4 pos) := by
  rcases valid_pos_is_0_1_2 pos h with rfl | rfl | rfl <;> simp [T4]
-- LLM HELPER
lemma T5_valid (pos : Int) (h : ValidPosition pos) : ValidPosition (T5 pos) := by
  rcases valid_pos_is_0_1_2 pos h with rfl | rfl | rfl <;> simp [T5]
-- LLM HELPER
lemma T6_valid (pos : Int) (h : ValidPosition pos) : ValidPosition (T6 pos) := by
  unfold T6; exact h
-- </vc-helpers>

-- <vc-definitions>
def solve (n x : Int) (h_precond : solve_precond n x) : Int :=
  let n_mod_6 := n % 6
  if n_mod_6 = 1 then T1 x
  else if n_mod_6 = 2 then T2 x
  else if n_mod_6 = 3 then T3 x
  else if n_mod_6 = 4 then T4 x
  else if n_mod_6 = 5 then T5 x
  else T6 x
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n x : Int) (result : Int) (h_precond : solve_precond n x) : Prop :=
  ValidPosition result

theorem solve_spec_satisfied (n x : Int) (h_precond : solve_precond n x) :
    solve_postcond n x (solve n x h_precond) h_precond := by
  unfold solve_postcond solve
  dsimp
  rcases h_precond with ⟨_, _, hx⟩
  split_ifs
  · exact T1_valid x hx
  · exact T2_valid x hx
  · exact T3_valid x hx
  · exact T4_valid x hx
  · exact T5_valid x hx
  · exact T6_valid x hx
-- </vc-theorems>
