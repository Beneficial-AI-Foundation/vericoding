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
def finalPosition (n x : Int) : Int :=
  let remainder := n % 4
  if remainder = 0 then x
  else if remainder = 1 then
    if x = 0 then 1
    else if x = 1 then 0
    else 2
  else if remainder = 2 then
    if x = 0 then 2
    else if x = 1 then 2
    else 1
  else -- remainder = 3
    if x = 0 then 0
    else if x = 1 then 1
    else 2
-- </vc-helpers>

-- <vc-definitions>
def solve (n x : Int) (h_precond : solve_precond n x) : Int :=
  finalPosition n x
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n x : Int) (result : Int) (h_precond : solve_precond n x) : Prop :=
  ValidPosition result

theorem solve_spec_satisfied (n x : Int) (h_precond : solve_precond n x) :
    solve_postcond n x (solve n x h_precond) h_precond := by
  unfold solve solve_postcond finalPosition ValidPosition
  rcases h_precond with ⟨h_n_ge, h_n_le, h_x_ge, h_x_le⟩
  have h_rem : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
    have h := Int.emod_nonneg n (by norm_num : (4 : Int) ≠ 0)
    have h' := Int.emod_lt_of_pos n (by norm_num : 0 < (4 : Int))
    interval_cases n % 4 <;> simp [*]
  have h_x_cases : x = 0 ∨ x = 1 ∨ x = 2 := by omega
  rcases h_rem with h0 | h1 | h2 | h3
  · -- n % 4 = 0
    simp [h0]
    exact ⟨h_x_ge, h_x_le⟩
  · -- n % 4 = 1  
    simp [h1]
    rcases h_x_cases with hx0 | hx1 | hx2 <;> simp [*] <;> omega
  · -- n % 4 = 2
    simp [h2]
    rcases h_x_cases with hx0 | hx1 | hx2 <;> simp [*] <;> omega
  · -- n % 4 = 3
    simp [h3]
    rcases h_x_cases with hx0 | hx1 | hx2 <;> simp [*] <;> omega
-- </vc-theorems>
