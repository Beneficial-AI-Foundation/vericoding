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
def runningMax (numbers: List Int) : List Int :=
match numbers with
| [] => []
| x :: xs => 
  let rest := runningMax xs
  match rest with
  | [] => [x]
  | y :: ys => (max x y) :: rest

-- LLM HELPER
lemma runningMax_length (numbers: List Int) : (runningMax numbers).length = numbers.length := by
  induction numbers with
  | nil => simp [runningMax]
  | cons x xs ih => 
    simp [runningMax]
    cases runningMax xs with
    | nil => simp [runningMax] at ih; simp [ih]
    | cons y ys => simp [ih]

-- LLM HELPER
lemma runningMax_mem (numbers: List Int) (i: Nat) (hi: i < numbers.length) : 
  (runningMax numbers)[i]! ∈ numbers.take (i + 1) := by
  induction numbers generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    simp [runningMax]
    cases h : runningMax xs with
    | nil => 
      simp [runningMax] at h
      have : xs = [] := by
        cases xs with
        | nil => rfl
        | cons y ys => simp [runningMax] at h
      simp [this] at hi
      cases i with
      | zero => simp [List.take]
      | succ j => simp at hi
    | cons y ys => 
      cases i with
      | zero => simp [List.take, max_def]; split_ifs <;> simp
      | succ j => 
        simp [List.take]
        simp at hi
        have : (runningMax xs)[j]! ∈ xs.take (j + 1) := ih j hi
        simp [max_def]
        split_ifs with h_cond
        · simp
        · exact List.mem_cons_of_mem x this

-- LLM HELPER
lemma runningMax_monotone (numbers: List Int) (i j: Nat) (hij: j ≤ i) (hi: i < numbers.length) : 
  numbers[j]! ≤ (runningMax numbers)[i]! := by
  induction numbers generalizing i j with
  | nil => simp at hi
  | cons x xs ih =>
    simp [runningMax]
    cases h : runningMax xs with
    | nil =>
      simp [runningMax] at h
      have : xs = [] := by
        cases xs with
        | nil => rfl
        | cons y ys => simp [runningMax] at h
      simp [this] at hi
      cases i with
      | zero => 
        cases j with
        | zero => simp [le_max_left]
        | succ k => simp at hij
      | succ k => simp at hi
    | cons head tail =>
      cases i with
      | zero =>
        cases j with
        | zero => simp [le_max_left]
        | succ k => simp at hij
      | succ k =>
        simp at hi
        cases j with
        | zero => simp [le_max_left]
        | succ l =>
          simp at hij
          have : xs[l]! ≤ (runningMax xs)[k]! := ih k l hij hi
          simp [le_max_right]
          exact this

def implementation (numbers: List Int) : List Int := runningMax numbers

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers := by
  simp [problem_spec, implementation]
  use runningMax numbers
  constructor
  · rfl
  · constructor
    · exact runningMax_length numbers
    · intro i hi
      constructor
      · exact runningMax_mem numbers i hi
      · intro j hj
        exact runningMax_monotone numbers i j hj hi