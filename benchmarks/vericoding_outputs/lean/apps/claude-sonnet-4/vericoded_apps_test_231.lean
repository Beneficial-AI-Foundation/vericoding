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
-- LLM HELPER: Helper lemmas for distance calculation
lemma distance_odd_positive (n a : Int) (h_valid : ValidInput n a) (h_odd : a % 2 = 1) :
    a / 2 + 1 > 0 := by
  have h_a_pos : a ≥ 1 := h_valid.2.2.1
  have h_div_nonneg : a / 2 ≥ 0 := by
    apply Int.ediv_nonneg
    · linarith
    · norm_num
  linarith

lemma distance_even_positive (n a : Int) (h_valid : ValidInput n a) (h_even : a % 2 = 0) :
    (n - a) / 2 + 1 > 0 := by
  have h_n_pos : n > 0 := h_valid.1
  have h_a_le_n : a ≤ n := h_valid.2.2.2
  have h_diff_nonneg : n - a ≥ 0 := Int.sub_nonneg_of_le h_a_le_n
  have h_div_nonneg : (n - a) / 2 ≥ 0 := by
    apply Int.ediv_nonneg
    · exact h_diff_nonneg
    · norm_num
  linarith
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
  unfold solve solve_postcond DistanceToHouse
  have h_valid := h_precond
  have h_a_pos : a ≥ 1 := h_valid.2.2.1
  have h_a_le_n : a ≤ n := h_valid.2.2.2
  split_ifs with h_odd
  · -- Case: a % 2 = 1
    exact distance_odd_positive n a h_valid h_odd
  · -- Case: a % 2 ≠ 1, so a % 2 = 0
    have h_even : a % 2 = 0 := by
      have h_a_int : a % 2 = 0 ∨ a % 2 = 1 := Int.emod_two_eq_zero_or_one a
      cases h_a_int with
      | inl h => exact h
      | inr h => contradiction
    exact distance_even_positive n a h_valid h_even
-- </vc-theorems>
