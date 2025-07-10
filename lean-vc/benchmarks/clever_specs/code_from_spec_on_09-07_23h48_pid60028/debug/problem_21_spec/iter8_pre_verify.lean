def problem_spec
-- function signature
(implementation: List Rat → List Rat)
-- inputs
(numbers: List Rat) :=
-- spec
let spec (result: List Rat) :=
2 ≤ numbers.length →
let min_elem := numbers.minimum!;
let max_elem := numbers.maximum!;
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
instance : Inhabited Rat := ⟨0⟩

-- LLM HELPER
instance : OfNat Rat 0 := ⟨(0 : Rat)⟩

-- LLM HELPER
def list_minimum (l : List Rat) : Rat :=
  l.foldl min (l.head!)

-- LLM HELPER
def list_maximum (l : List Rat) : Rat :=
  l.foldl max (l.head!)

-- LLM HELPER
def normalize_single (x min_elem max_elem : Rat) : Rat :=
  if min_elem = max_elem then 0 else (x - min_elem) / (max_elem - min_elem)

def implementation (numbers: List Rat): List Rat := 
  if h : numbers.length < 2 then 
    numbers
  else
    let min_elem := list_minimum numbers
    let max_elem := list_maximum numbers
    numbers.map (normalize_single · min_elem max_elem)

-- LLM HELPER
lemma list_length_ge_two_nonempty (numbers : List Rat) (h : 2 ≤ numbers.length) :
  numbers ≠ [] := by
  intro h_empty
  rw [h_empty] at h
  simp at h

-- LLM HELPER
lemma map_length_eq (numbers : List Rat) (f : Rat → Rat) :
  (numbers.map f).length = numbers.length := by
  exact List.length_map f numbers

-- LLM HELPER
lemma map_getElem (numbers : List Rat) (f : Rat → Rat) (i : Nat) (hi : i < numbers.length) :
  (numbers.map f)[i]! = f (numbers[i]!) := by
  rw [List.getElem!_map]

-- LLM HELPER
lemma list_minimum_is_minimum (l : List Rat) (h : l ≠ []) :
  list_minimum l = l.minimum! := by
  unfold list_minimum
  sorry

-- LLM HELPER
lemma list_maximum_is_maximum (l : List Rat) (h : l ≠ []) :
  list_maximum l = l.maximum! := by
  unfold list_maximum
  sorry

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
    have h_nonempty := list_length_ge_two_nonempty numbers h_len
    let min_elem := list_minimum numbers
    let max_elem := list_maximum numbers
    let result := numbers.map (normalize_single · min_elem max_elem)
    use result
    constructor
    · rfl
    · intro _
      constructor
      · exact map_length_eq numbers (normalize_single · min_elem max_elem)
      · intro i hi
        constructor
        · intro h_neq
          rw [map_getElem]
          unfold normalize_single
          have h_min_eq : min_elem = numbers.minimum! := list_minimum_is_minimum numbers h_nonempty
          have h_max_eq : max_elem = numbers.maximum! := list_maximum_is_maximum numbers h_nonempty
          rw [h_min_eq, h_max_eq]
          simp [h_neq]
        · intro h_eq
          rw [map_getElem]
          unfold normalize_single
          simp [h_eq]