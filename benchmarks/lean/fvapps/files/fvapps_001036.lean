-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sum_numbers (input : List String) : List String := sorry

theorem sum_numbers_length_matches_input {input : List String} :
  input.length = (sum_numbers input).length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sum_numbers_correct_sum {input : List String} {i : Nat} (h : i < input.length) :
  let nums := (input.get ⟨i,h⟩).split (· = ' ')
  let a := nums.get ⟨0, sorry⟩ |>.toInt!
  let b := nums.get ⟨1, sorry⟩ |>.toInt!
  (sum_numbers input).get ⟨i, by rw [←sum_numbers_length_matches_input]; exact h⟩ = toString (a + b) := sorry

theorem sum_numbers_result_strings {input : List String} {i : Nat} (h : i < input.length) :
  (sum_numbers input).get ⟨i, by rw [←sum_numbers_length_matches_input]; exact h⟩ matches ".*" := sorry

theorem sum_numbers_zeros {input : List String} (h : ∀ (i : Nat) (hi : i < input.length), input.get ⟨i,hi⟩ = "0 0") :
  ∀ (i : Nat) (hi : i < input.length), (sum_numbers input).get ⟨i, by rw [←sum_numbers_length_matches_input]; exact hi⟩ = "0" := sorry
-- </vc-theorems>