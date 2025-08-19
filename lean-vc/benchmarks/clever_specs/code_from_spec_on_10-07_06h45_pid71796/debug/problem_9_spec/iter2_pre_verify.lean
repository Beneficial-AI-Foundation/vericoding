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
match numbers with
| [] => []
| x :: xs => 
  let rest := implementation xs
  (x :: rest).scanl max x

-- LLM HELPER
lemma implementation_length (numbers: List Int) :
(implementation numbers).length = numbers.length := by
induction numbers with
| nil => simp [implementation]
| cons x xs ih => 
  simp [implementation]
  rw [List.length_scanl]
  simp [ih]

-- LLM HELPER
lemma scanl_max_property (l: List Int) (init: Int) (i: Nat) :
i < (l.scanl max init).length →
∃ j, j ≤ i ∧ (l.scanl max init)[i]! = max init (l.take i).foldl max init := by
sorry

-- LLM HELPER
lemma implementation_property (numbers: List Int) (i: Nat) :
i < numbers.length →
let result := implementation numbers
result[i]?.getD 0 ∈ numbers.take (i + 1) ∧
∀ j, j ≤ i → numbers[j]?.getD 0 ≤ result[i]?.getD 0 := by
intro h
induction numbers generalizing i with
| nil => simp at h
| cons x xs ih =>
  simp [implementation]
  cases i with
  | zero => 
    simp
    constructor
    · simp [List.mem_take]
    · intro j hj
      simp at hj
      simp [hj]
  | succ i' =>
    simp
    have h' : i' < xs.length := by
      simp at h
      exact Nat.lt_of_succ_lt_succ h
    have ih_applied := ih i' h'
    simp [implementation] at ih_applied
    constructor
    · sorry
    · sorry

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers := by
simp [problem_spec]
use implementation numbers
constructor
· rfl
constructor
· exact implementation_length numbers
· intro i h
  have h_bound : i < (implementation numbers).length := by
    rw [implementation_length]
    exact h
  -- Convert between different indexing notations
  have result_eq : (implementation numbers)[i]?.getD 0 = (implementation numbers)[i]! := by
    rw [List.getD_eq_get!]
    rw [List.get?_eq_get]
    exact h_bound
  rw [← result_eq]
  have numbers_eq : ∀ j, numbers[j]?.getD 0 = numbers[j]! := by
    intro j
    cases hj : j < numbers.length with
    | true => 
      rw [List.getD_eq_get!]
      rw [List.get?_eq_get]
      exact hj
    | false => 
      simp [List.get?_eq_none.mpr (Nat.not_lt.mp hj)]
      rw [List.get!_eq_getD]
      rw [List.getD_eq_default]
      exact Nat.not_lt.mp hj
  simp [numbers_eq]
  exact implementation_property numbers i h