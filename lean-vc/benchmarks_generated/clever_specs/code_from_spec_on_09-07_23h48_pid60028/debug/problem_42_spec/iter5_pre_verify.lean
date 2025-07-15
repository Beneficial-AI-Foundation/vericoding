def problem_spec
(implementation: List Int → List Int)
(numbers: List Int) :=
let spec (result: List Int) :=
  (result.length = numbers.length) ∧
  ∀ i, i < numbers.length →
  (Option.map (fun x => x + 1) numbers[i]?).getD 0 = (numbers[i]?.getD 0) + 1
∃ result, implementation numbers = result ∧
spec result

def implementation (numbers: List Int) : List Int := numbers.map (· + 1)

-- LLM HELPER
theorem map_length (f : Int → Int) (l : List Int) : (l.map f).length = l.length := by
  induction l with
  | nil => simp
  | cons h t ih => simp [List.map, ih]

-- LLM HELPER  
theorem map_get_option (f : Int → Int) (l : List Int) (i : Nat) : 
  (Option.map f l[i]?).getD 0 = f (l[i]?.getD 0) := by
  cases h : l[i]? with
  | none => simp [Option.map, Option.getD]
  | some val => simp [Option.map, h]

-- LLM HELPER
theorem map_get_eq (l : List Int) (i : Nat) (h : i < l.length) : 
  (l.map (· + 1))[i]? = Option.map (· + 1) l[i]? := by
  induction l generalizing i with
  | nil => simp at h
  | cons head tail ih =>
    cases i with
    | zero => simp [List.map]
    | succ j => 
      simp [List.map, List.get?]
      exact ih (Nat.lt_of_succ_lt_succ h)

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
      rw [map_get_eq numbers i h]
      exact map_get_option (· + 1) numbers i