def problem_spec
(implementation: List Int → Int → Bool)
(numbers: List Int)
(threshold: Int) :=
let numbers_below_threshold :=
  ∀ i, i < numbers.length → numbers[i]! < threshold;
let spec (res: Bool) :=
(numbers.length = 0 → res) ∧
(res ↔ numbers_below_threshold)
∃ result, implementation numbers threshold = result ∧
spec result

def implementation (numbers: List Int) (threshold: Int) : Bool := 
  numbers.all (fun x => x < threshold)

-- LLM HELPER
lemma all_iff_forall (numbers: List Int) (threshold: Int) :
  numbers.all (fun x => x < threshold) ↔ 
  ∀ i, i < numbers.length → numbers[i]! < threshold := by
  constructor
  · intro h i hi
    have : numbers[i]! ∈ numbers := List.getElem_mem numbers i hi
    exact List.all_eq_true.mp h (numbers[i]!) this
  · intro h
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_get.mp hx
    exact h i hi

-- LLM HELPER
lemma all_empty (threshold: Int) :
  ([] : List Int).all (fun x => x < threshold) = true := by
  rfl

theorem correctness
(numbers: List Int)
(threshold: Int)
: problem_spec implementation numbers threshold := by
  unfold problem_spec implementation
  use numbers.all (fun x => x < threshold)
  constructor
  · rfl
  · constructor
    · intro h
      rw [List.length_eq_zero] at h
      rw [h]
      exact all_empty threshold
    · rw [all_iff_forall]