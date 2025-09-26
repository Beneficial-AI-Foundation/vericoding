import Mathlib
-- <vc-preamble>
def ValidInput (n a : Int) : Prop :=
  n > 0 ∧ n % 2 = 0 ∧ 1 ≤ a ∧ a ≤ n

def DistanceToHouse (n a : Int) : Int :=
  if a % 2 = 1 then
    a / 2 + 1
  else
    (n - a) / 2 + 1

@[reducible, simp]
def solve_precond (n a : Int) : Prop :=
  ValidInput n a
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma distance_to_house_pos (n a : Int) (h : solve_precond n a) : 
    DistanceToHouse n a > 0 := by
  unfold DistanceToHouse solve_precond ValidInput at *
  obtain ⟨hn_pos, hn_even, ha_lower, ha_upper⟩ := h
  split_ifs with h_odd
  · -- Case: a is odd
    have : a ≥ 1 := ha_lower
    have : a / 2 ≥ 0 := Int.ediv_nonneg (by omega) (by norm_num)
    omega
  · -- Case: a is even
    have : n - a ≥ 0 := by omega
    have : (n - a) / 2 ≥ 0 := Int.ediv_nonneg (by omega) (by norm_num)
    omega
-- </vc-helpers>

-- <vc-definitions>
def solve (n a : Int) (h_precond : solve_precond n a) : Int :=
  DistanceToHouse n a
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n a : Int) (result: Int) (h_precond : solve_precond n a) : Prop :=
  result > 0

theorem solve_spec_satisfied (n a : Int) (h_precond : solve_precond n a) :
    solve_postcond n a (solve n a h_precond) h_precond := by
  unfold solve solve_postcond
  exact distance_to_house_pos n a h_precond
-- </vc-theorems>
