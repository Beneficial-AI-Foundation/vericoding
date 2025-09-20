-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_make_sequence_good (n : Nat) (sequence : List Int) : String :=
sorry

def sum_nonnegative (l : List Int) : Int :=
sorry

def sum_negative (l : List Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sequence_result_is_yes_or_no (n : Nat) (sequence : List Int) :
  let result := can_make_sequence_good n sequence
  result = "YES" ∨ result = "NO" :=
sorry

theorem yes_case_sums_property (n : Nat) (sequence : List Int) :
  can_make_sequence_good n sequence = "YES" →
  sum_nonnegative sequence ≥ Int.natAbs (sum_negative sequence) :=
sorry

theorem no_case_sums_property (n : Nat) (sequence : List Int) :
  can_make_sequence_good n sequence = "NO" →
  sum_nonnegative sequence < Int.natAbs (sum_negative sequence) :=
sorry

theorem single_element_sequence (x : Int) :
  can_make_sequence_good 1 [x] = (if x ≥ 0 then "YES" else "NO") :=
sorry

theorem sequence_length_valid (sequence : List Int) :
  let n := sequence.length
  let result := can_make_sequence_good n sequence
  result = "YES" ∨ result = "NO" :=
sorry
-- </vc-theorems>