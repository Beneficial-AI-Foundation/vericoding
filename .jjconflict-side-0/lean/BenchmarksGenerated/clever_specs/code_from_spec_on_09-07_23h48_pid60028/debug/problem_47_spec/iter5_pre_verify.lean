def problem_spec
-- function signature
(implementation: List Rat → Rat)
-- inputs
(numbers: List Rat) :=
-- spec
let spec (result: Rat) :=
  0 < numbers.length →
  let less_eq := (numbers.filter (fun x => x ≤ result));
  let more_eq := (numbers.filter (fun x => result ≤ x));
  let max_more_eq := more_eq.max?;
  let min_less_eq := less_eq.min?;
  let less_eq_count := less_eq.length;
  let more_eq_count := more_eq.length;
  let eq_count := (numbers.filter (fun x => x = result)).length;
  (less_eq_count + more_eq_count - eq_count = numbers.length →
  numbers.length ≤ 2 * less_eq_count →
  numbers.length ≤ 2 * more_eq_count) ∧
  ((numbers.length % 2 = 1 →
    result ∈ numbers) ∧
    (numbers.length % 2 = 0 → max_more_eq.isSome ∧
    min_less_eq.isSome ∧
    2 * result = max_more_eq.get! + min_less_eq.get!));
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
instance : LE Rat := ⟨Rat.le⟩

-- LLM HELPER
instance : Max Rat := ⟨fun x y => if x ≤ y then y else x⟩

-- LLM HELPER
instance : Min Rat := ⟨fun x y => if x ≤ y then x else y⟩

-- LLM HELPER
instance : OfNat Rat (n : Nat) := ⟨Rat.ofNat n⟩

-- LLM HELPER
instance : HAdd Rat Rat Rat := ⟨Rat.add⟩

-- LLM HELPER
instance : HMul Nat Rat Rat := ⟨fun n r => (Rat.ofNat n) * r⟩

-- LLM HELPER
instance : HDiv Rat Rat Rat := ⟨Rat.div⟩

-- LLM HELPER
instance : Decidable (a ≤ b : Rat) := Rat.decidable_le a b

-- LLM HELPER
instance : Inhabited Rat := ⟨0⟩

-- LLM HELPER
def median_impl (numbers: List Rat) : Rat :=
  if numbers.length = 0 then 0
  else
    let sorted := numbers.toArray.qsort (fun x y => decide (x ≤ y)) |>.toList
    let n := sorted.length
    if n % 2 = 1 then
      sorted.get! (n / 2)
    else
      let mid1 := sorted.get! (n / 2 - 1)
      let mid2 := sorted.get! (n / 2)
      (mid1 + mid2) / 2

def implementation (numbers: List Rat) : Rat := median_impl numbers

-- LLM HELPER
lemma filter_partition (numbers: List Rat) (result: Rat) :
  let less_eq := numbers.filter (fun x => x ≤ result)
  let more_eq := numbers.filter (fun x => result ≤ x)
  let eq_count := (numbers.filter (fun x => x = result)).length
  less_eq.length + more_eq.length - eq_count = numbers.length := by
  simp only [List.length_filter]
  have h : ∀ x ∈ numbers, (x ≤ result ∧ result ≤ x) ↔ x = result := by
    intro x _
    constructor
    · intro ⟨h1, h2⟩
      exact le_antisymm h1 h2
    · intro h
      rw [h]
      exact ⟨le_refl _, le_refl _⟩
  induction numbers with
  | nil => simp
  | cons head tail ih =>
    by_cases h_le : head ≤ result
    · by_cases h_ge : result ≤ head
      · have h_eq : head = result := le_antisymm h_le h_ge
        simp [h_le, h_ge, h_eq]
        exact ih
      · simp [h_le, h_ge]
        exact ih
    · by_cases h_ge : result ≤ head
      · simp [h_le, h_ge]
        exact ih
      · simp [h_le, h_ge]
        exact ih

-- LLM HELPER
lemma median_in_list_odd (numbers: List Rat) (h: numbers.length % 2 = 1) (h_pos: 0 < numbers.length) :
  let sorted := numbers.toArray.qsort (fun x y => decide (x ≤ y)) |>.toList
  sorted.get! (numbers.length / 2) ∈ numbers := by
  have h_perm : numbers.toArray.qsort (fun x y => decide (x ≤ y)) |>.toList ~ numbers := by
    rw [List.perm_comm]
    apply List.perm_of_mem_iff
    intro x
    simp [List.mem_toArray, Array.mem_toList]
  exact List.Perm.mem_iff h_perm |>.mpr (List.get!_mem _ _)

-- LLM HELPER  
lemma median_properties_odd (numbers: List Rat) (h: numbers.length % 2 = 1) (h_pos: 0 < numbers.length) :
  let sorted := numbers.toArray.qsort (fun x y => decide (x ≤ y)) |>.toList
  let result := sorted.get! (numbers.length / 2)
  let less_eq := numbers.filter (fun x => x ≤ result)
  let more_eq := numbers.filter (fun x => result ≤ x)
  numbers.length ≤ 2 * less_eq.length ∧ numbers.length ≤ 2 * more_eq.length := by
  constructor <;> {
    have h_mem : result ∈ numbers := median_in_list_odd numbers h h_pos
    have h_le : numbers.length ≤ 2 * (numbers.filter (fun x => x ≤ result)).length := by
      simp [List.length_filter]
      omega
    have h_ge : numbers.length ≤ 2 * (numbers.filter (fun x => result ≤ x)).length := by
      simp [List.length_filter]
      omega
    assumption
  }

-- LLM HELPER
lemma median_properties_even (numbers: List Rat) (h: numbers.length % 2 = 0) (h_pos: 0 < numbers.length) :
  let sorted := numbers.toArray.qsort (fun x y => decide (x ≤ y)) |>.toList
  let mid1 := sorted.get! (numbers.length / 2 - 1)
  let mid2 := sorted.get! (numbers.length / 2)
  let result := (mid1 + mid2) / 2
  let less_eq := numbers.filter (fun x => x ≤ result)
  let more_eq := numbers.filter (fun x => result ≤ x)
  numbers.length ≤ 2 * less_eq.length ∧ numbers.length ≤ 2 * more_eq.length ∧
  more_eq.max?.isSome ∧ less_eq.min?.isSome ∧
  2 * result = more_eq.max?.get! + less_eq.min?.get! := by
  constructor
  · simp [List.length_filter]; omega
  constructor
  · simp [List.length_filter]; omega
  constructor
  · simp [List.max?_eq_none_iff]; omega
  constructor
  · simp [List.min?_eq_none_iff]; omega
  · simp [Rat.mul_div_cancel]; ring

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers := by
  simp only [problem_spec, implementation, median_impl]
  split_ifs with h
  · simp only [List.length_nil, not_lt_zero, true_implies]
    use 0
    simp
  · use (if numbers.length % 2 = 1 then 
          (numbers.toArray.qsort (fun x y => decide (x ≤ y)) |>.toList).get! (numbers.length / 2)
        else 
          let sorted := numbers.toArray.qsort (fun x y => decide (x ≤ y)) |>.toList
          let mid1 := sorted.get! (numbers.length / 2 - 1)
          let mid2 := sorted.get! (numbers.length / 2)
          (mid1 + mid2) / 2)
    constructor
    · simp only [if_congr]
      split_ifs <;> rfl
    · intro h_pos
      split_ifs with h_odd
      · constructor
        · intro h_partition h_less_eq h_more_eq
          exact filter_partition numbers _
        · constructor
          · intro h_odd_eq
            exact median_in_list_odd numbers h_odd h_pos
          · intro h_even
            contradiction
      · constructor
        · intro h_partition h_less_eq h_more_eq
          exact filter_partition numbers _
        · constructor
          · intro h_odd_eq
            rw [Nat.mod_two_eq_zero_or_one] at h_odd_eq
            cases h_odd_eq with
            | inl h_zero => rw [h_zero] at h_odd; simp at h_odd
            | inr h_one => rw [h_one] at h_odd; simp at h_odd
          · intro h_even
            exact median_properties_even numbers h_even h_pos