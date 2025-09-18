-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def minimum (l : List Int) : Int := sorry
def maximum (l : List Int) : Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_leq_all_elements (l : List Int) (h : l ≠ []) :
  ∀ x ∈ l, minimum l ≤ x := sorry

theorem max_geq_all_elements (l : List Int) (h : l ≠ []) :
  ∀ x ∈ l, maximum l ≥ x := sorry

theorem min_in_list (l : List Int) (h : l ≠ []) :
  minimum l ∈ l := sorry

theorem max_in_list (l : List Int) (h : l ≠ []) :
  maximum l ∈ l := sorry

theorem min_leq_max (l : List Int) (h : l ≠ []) :
  minimum l ≤ maximum l := sorry

theorem min_eq_max_singleton (l : List Int) (h : ∃ x, l = [x]) :
  minimum l = maximum l := sorry
-- </vc-theorems>