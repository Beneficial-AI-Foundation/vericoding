def problem_spec
-- function signature
(implementation: List Rat → List Rat)
-- inputs
(numbers: List Rat) :=
-- spec
let spec (result: List Rat) :=
2 ≤ numbers.length →
let min_elem := numbers.min?.get!;
let max_elem := numbers.max?.get!;
let range := max_elem - min_elem;
result.length = numbers.length ∧
∀ i, i < numbers.length →
(min_elem ≠ max_elem →
result[i]! = (numbers[i]! - min_elem) / range) ∧
(min_elem = max_elem →
result[i]! = 0);
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def normalize_single (x min_elem max_elem : Rat) : Rat :=
if min_elem = max_elem then 0 else (x - min_elem) / (max_elem - min_elem)

def implementation (numbers: List Rat): List Rat := 
if h : numbers.length < 2 then 
  numbers
else
  let min_elem := numbers.min?.get!
  let max_elem := numbers.max?.get!
  numbers.map (fun x => normalize_single x min_elem max_elem)

-- LLM HELPER
lemma list_length_ge_two_has_min_max (numbers : List Rat) (h : 2 ≤ numbers.length) :
  numbers.min?.isSome ∧ numbers.max?.isSome := by
  constructor
  · apply List.min?_isSome_of_length_pos
    omega
  · apply List.max?_isSome_of_length_pos
    omega

-- LLM HELPER
lemma map_length_eq (numbers : List Rat) (f : Rat → Rat) :
  (numbers.map f).length = numbers.length := by
  exact List.length_map f numbers

-- LLM HELPER
lemma map_getElem (numbers : List Rat) (f : Rat → Rat) (i : Nat) (hi : i < numbers.length) :
  (numbers.map f)[i]! = f (numbers[i]!) := by
  rw [List.getElem!_map]
  simp

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers := by
  unfold problem_spec
  simp only [implementation]
  split_ifs with h
  · -- Case: numbers.length < 2
    use numbers
    constructor
    · rfl
    · intro h_len
      omega
  · -- Case: numbers.length ≥ 2
    push_neg at h
    have h_len : 2 ≤ numbers.length := by omega
    have ⟨min_some, max_some⟩ := list_length_ge_two_has_min_max numbers h_len
    let min_elem := numbers.min?.get!
    let max_elem := numbers.max?.get!
    let result := numbers.map (fun x => normalize_single x min_elem max_elem)
    use result
    constructor
    · rfl
    · intro _
      constructor
      · exact map_length_eq numbers (fun x => normalize_single x min_elem max_elem)
      · intro i hi
        constructor
        · intro h_neq
          rw [map_getElem]
          unfold normalize_single
          simp [h_neq]
        · intro h_eq
          rw [map_getElem]
          unfold normalize_single
          simp [h_eq]