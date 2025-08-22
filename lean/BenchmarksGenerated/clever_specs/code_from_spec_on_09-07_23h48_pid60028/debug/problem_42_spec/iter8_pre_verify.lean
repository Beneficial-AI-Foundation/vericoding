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
theorem get_some_of_lt (l : List Int) (i : Nat) (h : i < l.length) : 
  ∃ val, l[i]? = some val := by
  induction l generalizing i with
  | nil => simp at h
  | cons head tail ih =>
    cases i with
    | zero => simp [List.get?]
    | succ j => 
      simp [List.get?]
      apply ih
      exact Nat.lt_of_succ_lt_succ h

-- LLM HELPER
theorem spec_property (numbers : List Int) (i : Nat) (h : i < numbers.length) :
  (Option.map (fun x => x + 1) numbers[i]?).getD 0 = numbers[i]?.getD 0 + 1 := by
  obtain ⟨val, hval⟩ := get_some_of_lt numbers i h
  simp [Option.map, Option.getD, hval]

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
      exact spec_property numbers i h