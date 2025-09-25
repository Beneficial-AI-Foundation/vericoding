-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_valid_snake_procession (report : String) : String :=
sorry

def is_valid_segment (s₁ s₂ : Char) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_snake_formations (report : String) :
  (∀ i j : String.Pos, j.1 = i.1 + 1 →
    (report.get i = '.' ∨ (report.get i = 'H' ∧ report.get j = 'T'))) →
  check_valid_snake_procession report = "Valid" :=
sorry

theorem balanced_counts_if_valid (report : String) :
  check_valid_snake_procession report = "Valid" →
  let h_count := report.toList.filter (· = 'H') |>.length
  let t_count := report.toList.filter (· = 'T') |>.length
  h_count = t_count :=
sorry

theorem running_count_bounds_if_valid (report : String) (n : Nat) :
  check_valid_snake_procession report = "Valid" →
  n ≤ report.length →
  let h_count := (report.take n).toList.filter (· = 'H') |>.length
  let t_count := (report.take n).toList.filter (· = 'T') |>.length
  let count := h_count - t_count
  count ≥ 0 ∧ count ≤ 1 :=
sorry
-- </vc-theorems>