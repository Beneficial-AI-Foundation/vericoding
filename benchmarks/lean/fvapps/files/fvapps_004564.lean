-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_min_max (lst: List Int) : Option Int × Option Int := sorry

theorem get_min_max_properties (lst: List Int) :
  let result := get_min_max lst
  (lst = [] → result = (none, none)) ∧
  (lst ≠ [] →
    ∃ min_val max_val: Int,
      result.1 = some min_val ∧
      result.2 = some max_val ∧
      (∀ x ∈ lst, min_val ≤ x) ∧
      (∀ x ∈ lst, x ≤ max_val) ∧
      min_val ∈ lst ∧
      max_val ∈ lst) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_min_max_non_empty (lst: List Int) (h: lst ≠ []) :
  let result := get_min_max lst
  ∃ min_val max_val: Int,
    result.1 = some min_val ∧
    result.2 = some max_val ∧
    min_val ≤ max_val :=
sorry

theorem get_min_max_empty :
  get_min_max [] = (none, none) :=
sorry
-- </vc-theorems>