-- <vc-preamble>
def List.Sorted {α : Type} (r : α → α → Prop) (l : List α) : Prop :=
  ∀ i j (h1 : i < j) (h2 : j < l.length), r (l.get ⟨i, Nat.lt_trans h1 h2⟩) (l.get ⟨j, h2⟩)

structure Result where
  i : Nat
  n : Int
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def all_non_consecutive (arr : List Int) : List Result :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem consecutive_not_in_result (arr : List Int) (h : arr.length ≥ 2) :
  ∀ i (h1 : i < arr.length - 1),
  arr.get ⟨i+1, by omega⟩ = arr.get ⟨i, by omega⟩ + 1 →
  ¬∃ r ∈ all_non_consecutive arr, r.i = i + 1 :=
sorry

theorem non_consecutive_in_result (arr : List Int) (h : arr.length ≥ 2) :
  ∀ i, (h1 : i < arr.length - 1) →
  arr.get ⟨i+1, by omega⟩ ≠ arr.get ⟨i, by omega⟩ + 1 →
  ∃ r ∈ all_non_consecutive arr, r.i = i + 1 ∧ r.n = arr.get ⟨i+1, by omega⟩ :=
sorry

theorem indices_ascending (arr : List Int) (h : arr.length ≥ 2) :
  let result := all_non_consecutive arr
  result.length > 1 →
  List.Sorted (·≤·) (result.map Result.i) :=
sorry

theorem valid_indices (arr : List Int) (h : arr.length ≥ 2) :
  ∀ r ∈ all_non_consecutive arr,
  1 ≤ r.i ∧ r.i < arr.length :=
sorry
-- </vc-theorems>