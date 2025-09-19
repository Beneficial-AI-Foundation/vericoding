-- <vc-preamble>
def List.isPermutationOf (l1 l2 : List Int) : Prop :=
  ∀ x, (l1.filter (· = x)).length = (l2.filter (· = x)).length
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (arr : List Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_output_length {arr : List Int} (h : arr ≠ []) :
  (solve arr).length = arr.length :=
sorry

theorem solve_contains_same_elements {arr : List Int} (h : arr ≠ []) :
  (solve arr).isPermutationOf arr :=
sorry

theorem solve_maintains_frequency_order {arr : List Int} (h : arr ≠ []) :
  let freq := fun x => (arr.filter (· = x)).length
  ∀ i, i + 1 < (solve arr).length →
    let curr := (solve arr).get! i
    let next := (solve arr).get! (i+1)
    freq curr > freq next ∨
    (freq curr = freq next ∧ curr ≤ next) :=
sorry

theorem solve_idempotent {arr : List Int} (h : arr ≠ []) :
  solve (solve arr) = solve arr :=
sorry
-- </vc-theorems>