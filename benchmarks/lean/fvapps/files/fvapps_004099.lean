-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def uniq {α} [BEq α] (lst : List α) : List α :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem uniq_no_consecutive_duplicates {α} [BEq α] (lst : List α) :
  let result := uniq lst
  ∀ i, i < result.length - 1 → result[i]? ≠ result[i+1]? :=
sorry

theorem uniq_elements_from_original {α} [BEq α] (lst : List α) :
  ∀ x ∈ uniq lst, x ∈ lst :=
sorry

theorem uniq_length_le_input {α} [BEq α] (lst : List α) :
  (uniq lst).length ≤ lst.length :=
sorry

theorem uniq_preserves_first_occurrence {α} [BEq α] [DecidableEq α] (lst : List α) :
  ∀ val ∈ uniq lst,
  lst.findIdx? (fun x => decide (x = val)) = lst.findIdx? (fun x => decide (x = val)) :=
sorry

theorem uniq_all_none [BEq α] (lst : List (Option α)) (h : lst.length > 0) (h2 : ∀ x ∈ lst, x = none) :
  (uniq lst).length = 1 :=
sorry

theorem uniq_all_identical {α} [BEq α] (lst : List α) (x : α) (h : lst.length > 0) (h2 : ∀ y ∈ lst, y = x) :
  (uniq lst).length = 1 :=
sorry
-- </vc-theorems>