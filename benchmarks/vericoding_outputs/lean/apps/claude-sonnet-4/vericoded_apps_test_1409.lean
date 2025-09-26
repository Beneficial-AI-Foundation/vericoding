import Mathlib
-- <vc-preamble>
def count_eligible (participations : List Int) (k : Int) : Int :=
  match participations with
  | [] => 0
  | head :: tail => 
      (if 5 - head >= k then 1 else 0) + count_eligible tail k

@[reducible, simp]
def solve_precond (n k : Int) (participations : List Int) : Prop :=
  0 ≤ k ∧ k ≤ 5 ∧ n = participations.length ∧ 
  ∀ i, 0 ≤ i ∧ i < participations.length → 0 ≤ participations.get! i ∧ participations.get! i ≤ 5
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: count_eligible always returns non-negative values
lemma count_eligible_nonneg (participations : List Int) (k : Int) : 
  count_eligible participations k ≥ 0 := by
  induction participations with
  | nil => simp [count_eligible]
  | cons head tail ih => 
    simp [count_eligible]
    split_ifs
    · omega
    · simp only [zero_add]
      exact ih
-- </vc-helpers>

-- <vc-definitions>
def solve (n k : Int) (participations : List Int) (h_precond : solve_precond n k participations) : Int :=
  count_eligible participations k / 3
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n k : Int) (participations : List Int) (result : Int) (h_precond : solve_precond n k participations) : Prop :=
  result = (count_eligible participations k) / 3 ∧ result ≥ 0

theorem solve_spec_satisfied (n k : Int) (participations : List Int) (h_precond : solve_precond n k participations) :
    solve_postcond n k participations (solve n k participations h_precond) h_precond := by
  constructor
  · rfl
  · apply Int.ediv_nonneg
    · exact count_eligible_nonneg participations k  
    · norm_num
-- </vc-theorems>
