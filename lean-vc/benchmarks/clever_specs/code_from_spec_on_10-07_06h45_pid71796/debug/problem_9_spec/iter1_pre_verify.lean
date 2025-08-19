def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: List Int) :=
result.length = numbers.length ∧
∀ i, i < numbers.length →
(result[i]! ∈ numbers.take (i + 1) ∧
∀ j, j ≤ i → numbers[j]! ≤ result[i]!);
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def running_max_helper (numbers: List Int) (acc: List Int) : List Int :=
match numbers with
| [] => acc.reverse
| x :: xs => 
  let new_max := if acc.isEmpty then x else max x acc.head!
  running_max_helper xs (new_max :: acc)

def implementation (numbers: List Int) : List Int := 
running_max_helper numbers []

-- LLM HELPER
lemma running_max_helper_length (numbers: List Int) (acc: List Int) :
(running_max_helper numbers acc).length = numbers.length + acc.length := by
induction numbers generalizing acc with
| nil => simp [running_max_helper]
| cons x xs ih => 
  simp [running_max_helper]
  rw [ih]
  simp

-- LLM HELPER
lemma implementation_length (numbers: List Int) :
(implementation numbers).length = numbers.length := by
simp [implementation]
rw [running_max_helper_length]
simp

-- LLM HELPER
lemma running_max_helper_property (numbers: List Int) (acc: List Int) (i: Nat) :
i < numbers.length →
let result := running_max_helper numbers acc
i < result.length →
result[i]! ∈ numbers.take (i + 1) ∧
∀ j, j ≤ i → numbers[j]! ≤ result[i]! := by
sorry

-- LLM HELPER
lemma implementation_property (numbers: List Int) (i: Nat) :
i < numbers.length →
let result := implementation numbers
result[i]! ∈ numbers.take (i + 1) ∧
∀ j, j ≤ i → numbers[j]! ≤ result[i]! := by
intro h
simp [implementation]
have h_len : i < (running_max_helper numbers []).length := by
  rw [running_max_helper_length]
  simp
  exact h
exact running_max_helper_property numbers [] i h h_len

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers := by
simp [problem_spec]
use implementation numbers
constructor
· rfl
· constructor
  · exact implementation_length numbers
  · intro i h
    exact implementation_property numbers i h