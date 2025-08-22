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

def implementation (numbers: List Int) : List Int := 
  match numbers with
  | [] => []
  | x :: xs => 
    let rest := implementation xs
    x :: rest.map (max x)

-- LLM HELPER
lemma implementation_length (numbers: List Int) : (implementation numbers).length = numbers.length := by
  induction numbers with
  | nil => simp [implementation]
  | cons x xs ih => 
    simp [implementation]
    simp [List.length_map, ih]

-- LLM HELPER
lemma implementation_mem (numbers: List Int) (i: Nat) (hi: i < numbers.length) : 
  (implementation numbers)[i]?.getD 0 ∈ numbers.take (i + 1) := by
  induction numbers generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    simp [implementation]
    cases i with
    | zero => 
      simp [List.take]
      simp [List.getElem?_cons_zero]
    | succ j => 
      simp [List.take]
      simp at hi
      have h_len : j < (implementation xs).length := by
        rw [implementation_length]
        exact hi
      have h_map : ((implementation xs).map (max x))[j]?.getD 0 = max x ((implementation xs)[j]?.getD 0) := by
        simp [List.getElem?_map]
        rw [List.getElem?_eq_getElem h_len]
        simp
      simp [List.getElem?_cons_succ]
      rw [h_map]
      have : (implementation xs)[j]?.getD 0 ∈ xs.take (j + 1) := ih j hi
      simp [max_def]
      split_ifs with h_cond
      · simp
      · exact List.mem_cons_of_mem x this

-- LLM HELPER
lemma implementation_monotone (numbers: List Int) (i j: Nat) (hij: j ≤ i) (hi: i < numbers.length) : 
  numbers[j]?.getD 0 ≤ (implementation numbers)[i]?.getD 0 := by
  induction numbers generalizing i j with
  | nil => simp at hi
  | cons x xs ih =>
    simp [implementation]
    cases i with
    | zero => 
      cases j with
      | zero => 
        simp [List.getElem?_cons_zero]
        simp [le_refl]
      | succ k => simp at hij
    | succ k =>
      simp at hi
      cases j with
      | zero => 
        have h_len : k < (implementation xs).length := by
          rw [implementation_length]
          exact hi
        have h_map : ((implementation xs).map (max x))[k]?.getD 0 = max x ((implementation xs)[k]?.getD 0) := by
          simp [List.getElem?_map]
          rw [List.getElem?_eq_getElem h_len]
          simp
        simp [List.getElem?_cons_zero, List.getElem?_cons_succ]
        rw [h_map]
        simp [le_max_left]
      | succ l =>
        simp at hij
        have h_len : k < (implementation xs).length := by
          rw [implementation_length]
          exact hi
        have h_map : ((implementation xs).map (max x))[k]?.getD 0 = max x ((implementation xs)[k]?.getD 0) := by
          simp [List.getElem?_map]
          rw [List.getElem?_eq_getElem h_len]
          simp
        simp [List.getElem?_cons_succ]
        rw [h_map]
        have : xs[l]?.getD 0 ≤ (implementation xs)[k]?.getD 0 := ih k l hij hi
        exact le_trans this (le_max_right x ((implementation xs)[k]?.getD 0))

-- LLM HELPER
lemma getElem_bang_eq_getElem_getD (l: List Int) (i: Nat) (hi: i < l.length) : 
  l[i]! = l[i]?.getD 0 := by
  simp [List.getElem!_eq_getElem, List.getElem?_eq_getElem hi]

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers := by
  simp [problem_spec]
  use implementation numbers
  constructor
  · rfl
  · constructor
    · exact implementation_length numbers
    · intro i hi
      constructor
      · rw [getElem_bang_eq_getElem_getD]
        exact implementation_mem numbers i hi
      · intro j hij
        rw [getElem_bang_eq_getElem_getD, getElem_bang_eq_getElem_getD]
        exact implementation_monotone numbers i j hij hi