-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (arr : List Int) : List Int :=
  sorry

def list_max (l : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_maintains_elements {arr : List Int} (h : arr ≠ []) :
  let result := solve arr
  result.length = arr.length ∧
  ∀ x, (result.count x = arr.count x) :=
sorry

theorem solve_alternates_high_low {arr : List Int} (h : arr.length ≥ 2) :
  let result := solve arr
  ∀ i, i + 1 < result.length → i % 2 = 0 →
  (result.get ⟨i, sorry⟩) ≥ (result.get ⟨i+1, sorry⟩) :=
sorry

theorem solve_first_element_is_max {arr : List Int} (h : arr ≠ []) :
  let result := solve arr
  ∀ i, i < result.length →
  (result.get ⟨0, sorry⟩) ≥ (result.get ⟨i, sorry⟩) :=
sorry

theorem solve_empty_and_single {arr : List Int} :
  arr.length ≤ 1 → solve arr = arr :=
sorry
-- </vc-theorems>