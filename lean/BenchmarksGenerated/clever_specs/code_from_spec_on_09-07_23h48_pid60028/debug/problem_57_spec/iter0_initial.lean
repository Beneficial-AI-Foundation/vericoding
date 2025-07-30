def problem_spec
-- function signature
(implementation: List Int → Bool)
-- inputs
(numbers: List Int) :=
let non_ordered := ∃ i j,
i < numbers.length - 1 ∧
j < numbers.length - 1 ∧
(numbers[i]! < numbers[i+1]!) ∧
(numbers[j+1]! < numbers[j]!);
-- spec
let spec (result: Bool) :=
  1 < numbers.length →
  result ↔ ¬non_ordered;
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def is_monotonic (numbers: List Int) : Bool :=
  match numbers with
  | [] => true
  | [_] => true
  | x :: y :: rest => 
    if x <= y then is_monotonic (y :: rest)
    else if x >= y then is_monotonic_desc (y :: rest)
    else false

-- LLM HELPER
def is_monotonic_desc (numbers: List Int) : Bool :=
  match numbers with
  | [] => true
  | [_] => true
  | x :: y :: rest => x >= y && is_monotonic_desc (y :: rest)

def implementation (numbers: List Int) : Bool := is_monotonic numbers

-- LLM HELPER
lemma is_monotonic_correct (numbers: List Int) : 
  1 < numbers.length → 
  (is_monotonic numbers ↔ ¬∃ i j, i < numbers.length - 1 ∧ j < numbers.length - 1 ∧ 
    (numbers[i]! < numbers[i+1]!) ∧ (numbers[j+1]! < numbers[j]!)) := by
  intro h
  constructor
  · intro h_mono
    intro ⟨i, j, hi, hj, h_inc, h_dec⟩
    -- If the list is monotonic, it cannot have both increasing and decreasing adjacent pairs
    sorry
  · intro h_not_non_ordered
    -- If there's no violation of monotonicity, then the list is monotonic
    sorry

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers := by
  use is_monotonic numbers
  constructor
  · rfl
  · intro h
    exact is_monotonic_correct numbers h