def problem_spec
-- function signature
(impl: List Int → List Int)
-- inputs
(xs: List Int) :=
-- spec
let spec (result: List Int) :=
  result.length = xs.length - 1 ∧
  result = (check_derivative xs.reverse).reverse
-- program terminates
∃ result, impl xs = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def check_derivative (xs: List Int) : List Int :=
  match xs with
  | [] => []
  | [_] => []
  | a :: b :: rest => (b - a) :: check_derivative (b :: rest)

def implementation (xs: List Int) : List Int := 
  (check_derivative xs.reverse).reverse

-- LLM HELPER
lemma check_derivative_length (xs: List Int) : 
  (check_derivative xs).length = xs.length - 1 := by
  induction xs with
  | nil => simp [check_derivative]
  | cons h t ih =>
    cases t with
    | nil => simp [check_derivative]
    | cons h' t' => 
      simp [check_derivative]
      rw [ih]
      simp [Nat.add_sub_cancel]

-- LLM HELPER
lemma reverse_length (xs: List Int) : xs.reverse.length = xs.length := by
  simp [List.length_reverse]

theorem correctness
(xs: List Int)
: problem_spec implementation xs := by
  simp [problem_spec, implementation]
  use (check_derivative xs.reverse).reverse
  constructor
  · rfl
  · constructor
    · simp [check_derivative_length, reverse_length]
    · rfl