def problem_spec
(implementation: List Int → List Int)
(numbers: List Int) :=
let spec (result: List Int) :=
  result.length = numbers.length ∧
  ∀ i, i < numbers.length →
    result[i]! = numbers[i]! * 2
∃ result, implementation numbers = result ∧
spec result

def implementation (numbers: List Int) : List Int := numbers.map (· * 2)

-- LLM HELPER
lemma map_length {α β : Type*} (f : α → β) (l : List α) : (l.map f).length = l.length := by
  induction l with
  | nil => simp
  | cons h t ih => simp [List.map, ih]

-- LLM HELPER
lemma map_getElem {α β : Type*} (f : α → β) (l : List α) (i : Nat) (h : i < l.length) : 
  (l.map f)[i]! = f (l[i]!) := by
  rw [List.getElem_map]

theorem correctness
(numbers : List Int)
: problem_spec implementation numbers := by
  use numbers.map (· * 2)
  constructor
  · rfl
  · constructor
    · exact map_length (· * 2) numbers
    · intro i hi
      exact map_getElem (· * 2) numbers i hi