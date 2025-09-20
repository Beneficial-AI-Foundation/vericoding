-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def average (l : List Int) : Int :=
  sorry

def list_min (l : List Int) : Int :=
  sorry

def list_max (l : List Int) : Int :=
  sorry

def list_sum (l : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem average_in_range (l : List Int) (h : l ≠ []) :
  let result := average l
  let min_val := list_min l
  let max_val := list_max l
  min_val ≤ result ∧ result ≤ max_val := by
  sorry

theorem average_close_to_mean (l : List Int) (h : l ≠ []) :
  let result := average l
  let mean := (list_sum l) / (List.length l)
  (result - mean) < 1 ∧ (mean - result) < 1 := by
  sorry

theorem average_shift (l : List Int) (shift : Int) (h : l ≠ []) :
  average (List.map (· + shift) l) = average l + shift := by
  sorry

theorem average_empty :
  average [] = 0 ∧ False := by
  sorry
-- </vc-theorems>