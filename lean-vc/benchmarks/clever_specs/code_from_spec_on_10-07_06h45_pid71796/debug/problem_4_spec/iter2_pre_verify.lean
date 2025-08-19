def problem_spec
-- function signature
(implementation: List Rat → Rat)
-- inputs
(numbers: List Rat) :=
-- spec
let spec (result: Rat):=
0 < numbers.length →
0 ≤ result ∧
result * numbers.length * numbers.length =
(numbers.map (fun x => abs (x * numbers.length - numbers.sum))).sum;
-- program terminates
∃ result, implementation numbers = result ∧
-- return value satisfies spec
spec result

def implementation (numbers: List Rat) : Rat :=
if numbers.length = 0 then 0 else
(numbers.map (fun x => abs (x * numbers.length - numbers.sum))).sum / (numbers.length * numbers.length)

-- LLM HELPER
lemma abs_nonneg (x : Rat) : 0 ≤ abs x := abs_nonneg x

-- LLM HELPER
lemma sum_nonneg_of_nonneg {l : List Rat} (h : ∀ x ∈ l, 0 ≤ x) : 0 ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp [List.sum_cons]
    apply add_nonneg
    · exact h a (List.mem_cons_self a l)
    · exact ih (fun x hx => h x (List.mem_cons_of_mem a hx))

-- LLM HELPER
lemma map_abs_nonneg (numbers : List Rat) : 0 ≤ (numbers.map (fun x => abs (x * numbers.length - numbers.sum))).sum := by
  apply sum_nonneg_of_nonneg
  intros x hx
  simp at hx
  obtain ⟨y, _, rfl⟩ := hx
  exact abs_nonneg _

-- LLM HELPER
lemma div_nonneg_of_nonneg_pos {a b : Rat} (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b := by
  exact div_nonneg ha (le_of_lt hb)

-- LLM HELPER
lemma length_pos_of_pos {numbers : List Rat} (h : 0 < numbers.length) : 0 < (numbers.length : Rat) := by
  simp
  exact Nat.cast_pos.mpr h

-- LLM HELPER
lemma length_sq_pos_of_pos {numbers : List Rat} (h : 0 < numbers.length) : 0 < (numbers.length : Rat) * (numbers.length : Rat) := by
  have h_pos : 0 < (numbers.length : Rat) := length_pos_of_pos h
  exact mul_pos h_pos h_pos

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers := by
  unfold problem_spec implementation
  by_cases h : numbers.length = 0
  · simp [h]
    use 0
    simp
    intro h_contra
    rw [h] at h_contra
    exact lt_irrefl 0 h_contra
  · simp [h]
    use (numbers.map (fun x => abs (x * numbers.length - numbers.sum))).sum / (numbers.length * numbers.length)
    constructor
    · rfl
    · intro h_pos
      constructor
      · apply div_nonneg_of_nonneg_pos
        · exact map_abs_nonneg numbers
        · exact length_sq_pos_of_pos h_pos
      · field_simp