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
  x :: rest.map (max x)

-- LLM HELPER
lemma runningMax_length (numbers: List Int) : (runningMax numbers).length = numbers.length := by
  induction numbers with
  | nil => simp [runningMax]
  | cons x xs ih => 
    simp [runningMax]
    simp [List.length_map, ih]

-- LLM HELPER
lemma runningMax_mem (numbers: List Int) (i: Nat) (hi: i < numbers.length) : 
  (runningMax numbers)[i]! ∈ numbers.take (i + 1) := by
  induction numbers generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    simp [runningMax]
    cases i with
    | zero => simp [List.take]
    | succ j => 
      simp [List.take]
      simp at hi
      have h_map : ((runningMax xs).map (max x))[j]! = max x (runningMax xs)[j]! := by
        simp [List.getElem_map]
        have : j < (runningMax xs).length := by
          rw [runningMax_length]
          exact hi
        simp [this]
      rw [h_map]
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
    cases i with
    | zero => 
      cases j with
      | zero => simp [le_refl]
      | succ k => simp at hij
    | succ k =>
      simp at hi
      cases j with
      | zero => 
        have h_map : ((runningMax xs).map (max x))[k]! = max x (runningMax xs)[k]! := by
          simp [List.getElem_map]
          have : k < (runningMax xs).length := by
            rw [runningMax_length]
            exact hi
          simp [this]
        rw [h_map]
        simp [le_max_left]
      | succ l =>
        simp at hij
        have h_map : ((runningMax xs).map (max x))[k]! = max x (runningMax xs)[k]! := by
          simp [List.getElem_map]
          have : k < (runningMax xs).length := by
            rw [runningMax_length]
            exact hi
          simp [this]
        rw [h_map]
        have : xs[l]! ≤ (runningMax xs)[k]! := ih k l hij hi
        exact le_trans this (le_max_right x (runningMax xs)[k]!)

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