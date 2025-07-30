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

-- LLM HELPER
lemma abs_nonneg (x : Rat) : 0 ≤ abs x := abs_nonneg x

-- LLM HELPER
lemma sum_nonneg_of_nonneg {α : Type*} (l : List α) (f : α → Rat) (h : ∀ x ∈ l, 0 ≤ f x) : 0 ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp [List.map_cons, List.sum_cons]
    apply add_nonneg
    · exact h a (List.mem_cons_self a l)
    · exact ih (fun x hx => h x (List.mem_cons_of_mem a hx))

-- LLM HELPER
lemma div_nonneg_of_nonneg_pos (a b : Rat) (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b := by
  rw [div_nonneg_iff]
  left
  exact ⟨ha, hb⟩

def implementation (numbers: List Rat) : Rat := 
  if numbers.length = 0 then 0
  else (numbers.map (fun x => abs (x * numbers.length - numbers.sum))).sum / (numbers.length * numbers.length)

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers := by
  unfold problem_spec
  use implementation numbers
  constructor
  · rfl
  · intro h
    unfold implementation
    simp [if_neg (ne_of_gt h)]
    constructor
    · apply div_nonneg_of_nonneg_pos
      · apply sum_nonneg_of_nonneg
        intro x hx
        exact abs_nonneg _
      · apply mul_pos
        · exact Nat.cast_pos.mpr h
        · exact Nat.cast_pos.mpr h
    · rw [div_mul_cancel]
      apply ne_of_gt
      apply mul_pos
      · exact Nat.cast_pos.mpr h
      · exact Nat.cast_pos.mpr h