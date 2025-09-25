-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_length_xd_sequence (n : Nat) : String := sorry

theorem min_length_xd_sequence_only_contains_x_d (n : Nat) :
  let result := min_length_xd_sequence n
  ∀ c ∈ result.data, c = 'X' ∨ c = 'D' := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_length_xd_sequence_has_n_subsequences (n : Nat) :
  let result := min_length_xd_sequence n
  let x_count := (result.data.filter (· = 'X')).length
  let d_count := (result.data.filter (· = 'D')).length
  x_count * d_count = n := sorry

theorem min_length_xd_sequence_min_length (n : Nat) : 
  let result := min_length_xd_sequence n
  result.length ≥ 2 ∧
  ∀ (shorter : String), shorter.length = result.length - 1 →
  let x_shorter := (shorter.data.filter (· = 'X')).length
  let d_shorter := (shorter.data.filter (· = 'D')).length
  x_shorter * d_shorter < n := sorry
-- </vc-theorems>