def problem_spec
-- function signature
(impl: List Rat → Int)
-- inputs
(numbers: List Rat) :=
let isEven (n : Rat) := n.num % 2 = 0;
let isNegative (n : Rat) := n < 0;
let isNotInteger (n : Rat) := n.den ≠ 1;
-- spec
let spec (result: Int) :=
0 < numbers.length →
0 ≤ result ∧
if numbers.length = 1
then result = if (isEven numbers[0]! ∨ isNegative numbers[0]! ∨ isNotInteger numbers[0]!) then (0 : Int) else numbers[0]!.floor ^ 2
else result = if (isEven numbers[0]! ∨ isNegative numbers[0]! ∨ isNotInteger numbers[0]!) then (0 : Int) else numbers[0]!.floor ^ 2 + impl numbers.tail
-- program terminates
∃ result, impl numbers = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def isEven (n : Rat) : Bool := n.num % 2 = 0

-- LLM HELPER
def isNegative (n : Rat) : Bool := n < 0

-- LLM HELPER
def isNotInteger (n : Rat) : Bool := n.den ≠ 1

def implementation (numbers: List Rat) : Int := 
  match numbers with
  | [] => 0
  | [x] => 
    if isEven x ∨ isNegative x ∨ isNotInteger x then 0 else x.floor ^ 2
  | x :: xs => 
    if isEven x ∨ isNegative x ∨ isNotInteger x then 0 + implementation xs else x.floor ^ 2 + implementation xs

-- LLM HELPER
lemma implementation_nonneg (numbers: List Rat) : 0 ≤ implementation numbers := by
  induction numbers with
  | nil => simp [implementation]
  | cons x xs ih =>
    simp [implementation]
    split_ifs with h
    · exact ih
    · apply add_nonneg
      · exact sq_nonneg _
      · exact ih

-- LLM HELPER
instance : DecidableEq Int := by infer_instance

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers := by
  simp [problem_spec]
  use implementation numbers
  constructor
  · rfl
  · intro h
    constructor
    · exact implementation_nonneg numbers
    · cases numbers with
      | nil => contradiction
      | cons x xs =>
        cases xs with
        | nil => 
          simp [implementation, List.length]
          rfl
        | cons y ys =>
          simp [implementation, List.length, List.tail]
          rfl