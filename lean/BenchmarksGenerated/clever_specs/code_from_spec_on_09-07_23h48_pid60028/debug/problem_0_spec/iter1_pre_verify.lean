def specification
(impl: List Rat → Rat → Bool) (numbers: List Rat) (threshold: Rat) :=
  let numbers_within_threshold :=
    (∃ i j, i < numbers.length ∧ j < numbers.length ∧
    i ≠ j ∧ |numbers.get! i - numbers.get! j| < threshold);
  let spec (res: Bool) :=
    numbers.length > 1 → if res then numbers_within_threshold else ¬numbers_within_threshold;
    ∃ result, impl numbers threshold = result ∧ spec result

-- LLM HELPER
def has_close_pair (numbers: List Rat) (threshold: Rat) : Bool :=
  numbers.any (fun x => numbers.any (fun y => x ≠ y ∧ |x - y| < threshold))

def implementation (numbers: List Rat) (threshold: Rat) : Bool := 
  has_close_pair numbers threshold

-- LLM HELPER
lemma has_close_pair_correct (numbers: List Rat) (threshold: Rat) :
  has_close_pair numbers threshold = true ↔ 
  (∃ i j, i < numbers.length ∧ j < numbers.length ∧ i ≠ j ∧ |numbers.get! i - numbers.get! j| < threshold) := by
  constructor
  · intro h
    unfold has_close_pair at h
    simp [List.any_eq_true] at h
    obtain ⟨x, hx_mem, hy⟩ := h
    simp [List.any_eq_true] at hy
    obtain ⟨y, hy_mem, hxy⟩ := hy
    simp at hxy
    obtain ⟨hne, hdiff⟩ := hxy
    obtain ⟨i, hi_lt, hi_eq⟩ := List.get!_mem hx_mem
    obtain ⟨j, hj_lt, hj_eq⟩ := List.get!_mem hy_mem
    use i, j
    constructor
    · exact hi_lt
    constructor
    · exact hj_lt
    constructor
    · intro heq
      rw [heq] at hi_eq
      rw [hi_eq, hj_eq] at hne
      exact hne rfl
    · rw [←hi_eq, ←hj_eq]
      exact hdiff
  · intro h
    obtain ⟨i, j, hi_lt, hj_lt, hij, hdiff⟩ := h
    unfold has_close_pair
    simp [List.any_eq_true]
    use numbers.get! i
    constructor
    · exact List.get!_mem hi_lt
    simp [List.any_eq_true]
    use numbers.get! j
    constructor
    · exact List.get!_mem hj_lt
    simp
    constructor
    · intro heq
      have : i = j := by
        apply List.get!_inj
        · exact hi_lt
        · exact hj_lt
        · exact heq
      exact hij this
    · exact hdiff

-- LLM HELPER
lemma has_close_pair_false (numbers: List Rat) (threshold: Rat) :
  has_close_pair numbers threshold = false ↔ 
  ¬(∃ i j, i < numbers.length ∧ j < numbers.length ∧ i ≠ j ∧ |numbers.get! i - numbers.get! j| < threshold) := by
  rw [←has_close_pair_correct]
  simp [Bool.not_eq_true]

theorem correctness (numbers: List Rat) (threshold: Rat)
: specification implementation numbers threshold := by
  unfold specification implementation
  simp
  use has_close_pair numbers threshold
  constructor
  · rfl
  · intro h
    cases' h_eq : has_close_pair numbers threshold with
    · simp [h_eq]
      exact (has_close_pair_false numbers threshold).mp h_eq
    · simp [h_eq]
      exact (has_close_pair_correct numbers threshold).mp h_eq