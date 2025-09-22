-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.toMultiset : List α → List α := id

def validate_stack_sequences (pushed : List Int) (popped : List Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem identical_sequences_valid {nums : List Int} (h : nums.length > 0) :
  validate_stack_sequences nums nums = true :=
sorry

theorem reverse_sequences_valid {nums : List Int} (h : nums.length > 0) :
  validate_stack_sequences nums nums.reverse = true :=
sorry

theorem permutations_have_consistent_length {nums popped : List Int} (h : nums.length > 0) :
  validate_stack_sequences nums popped = (nums.length = popped.length) :=
sorry

theorem shuffled_sequence_properties {nums popped : List Int} (h : nums.length > 0) :
  validate_stack_sequences nums popped = true →
  nums.toMultiset = popped.toMultiset :=
sorry
-- </vc-theorems>