def problem_spec
(implementation: List Int → List Int)
(numbers: List Int) :=
let spec (result: List Int) :=
  (result.length = numbers.length) ∧
  ∀ i, i < numbers.length →
  result[i]! = numbers[i]! + 1
∃ result, implementation numbers = result ∧
spec result

def implementation (numbers: List Int) : List Int := numbers.map (· + 1)

-- LLM HELPER
theorem map_length (f : Int → Int) (l : List Int) : (l.map f).length = l.length := by
  induction l with
  | nil => simp
  | cons h t ih => simp [List.map, ih]

-- LLM HELPER
theorem map_get (f : Int → Int) (l : List Int) (i : Nat) (h : i < l.length) : 
  (l.map f)[i]! = f (l[i]!) := by
  induction l generalizing i with
  | nil => simp at h
  | cons head tail ih => 
    cases i with
    | zero => simp [List.map]
    | succ j => 
      simp [List.map, List.get!]
      have h' : j < tail.length := by
        simp at h
        exact h
      exact ih h'

theorem correctness
(numbers : List Int)
: problem_spec implementation numbers := by
  simp [problem_spec, implementation]
  use numbers.map (· + 1)
  constructor
  · rfl
  · constructor
    · exact map_length (· + 1) numbers
    · intro i h
      rw [map_get (· + 1) numbers i h]
      simp