def problem_spec
(implementation: List (List Nat) → Nat → Nat)
(grid: List (List Nat))
(capacity: Nat) :=
let spec (result : Nat) :=
  (grid.all (fun row => row.all (fun cell => cell = 0 ∨ cell = 1))) →
  (∃ len : Nat, grid.all (fun row => row.length = len)) →
  (result = 0 ↔ grid.length = 0) ∧
  (grid.length > 0 →
    let well_water_count := grid.head!.sum;
    result - (well_water_count / capacity) - (if well_water_count % capacity > 0 then 1 else 0) = implementation grid.tail! capacity)
∃ result,
  implementation grid capacity = result ∧
  spec result

-- LLM HELPER
def buckets_needed (water_count: Nat) (capacity: Nat) : Nat :=
  (water_count / capacity) + (if water_count % capacity > 0 then 1 else 0)

def implementation (grid: List (List Nat)) (capacity: Nat) : Nat := 
  match grid with
  | [] => 0
  | row :: rest => buckets_needed row.sum capacity + implementation rest capacity

-- LLM HELPER
lemma buckets_needed_zero (capacity: Nat) : buckets_needed 0 capacity = 0 := by
  simp [buckets_needed]

-- LLM HELPER
lemma implementation_empty (capacity: Nat) : implementation [] capacity = 0 := by
  simp [implementation]

-- LLM HELPER
lemma implementation_cons (row: List Nat) (rest: List (List Nat)) (capacity: Nat) :
  implementation (row :: rest) capacity = buckets_needed row.sum capacity + implementation rest capacity := by
  simp [implementation]

-- LLM HELPER
lemma implementation_nonneg (grid: List (List Nat)) (capacity: Nat) : implementation grid capacity ≥ 0 := by
  induction grid with
  | nil => simp [implementation_empty]
  | cons head tail ih => 
    simp [implementation_cons]
    apply Nat.zero_le

-- LLM HELPER
lemma implementation_zero_iff_empty (grid: List (List Nat)) (capacity: Nat) (h_cap: capacity > 0) : 
  implementation grid capacity = 0 ↔ grid = [] := by
  constructor
  · intro h
    induction grid with
    | nil => rfl
    | cons head tail ih =>
      simp [implementation_cons] at h
      have h_head_zero : buckets_needed head.sum capacity = 0 := by
        have h_tail_nonneg : implementation tail capacity ≥ 0 := implementation_nonneg tail capacity
        omega
      have h_tail_zero : implementation tail capacity = 0 := by
        have h_buckets_nonneg : buckets_needed head.sum capacity ≥ 0 := Nat.zero_le _
        omega
      have h_head_sum_zero : head.sum = 0 := by
        simp [buckets_needed] at h_head_zero
        by_cases h_mod : head.sum % capacity > 0
        · simp [h_mod] at h_head_zero
          have : head.sum / capacity + 1 = 0 := h_head_zero
          omega
        · simp [h_mod] at h_head_zero
          have : head.sum / capacity = 0 := h_head_zero
          have : head.sum < capacity := Nat.div_eq_zero_iff_lt.mp this
          have : head.sum % capacity = 0 := Nat.eq_zero_of_le_zero (le_of_not_gt h_mod)
          exact Nat.eq_zero_of_zero_dvd ⟨this⟩ ‹head.sum < capacity›
      have h_tail_empty : tail = [] := ih h_tail_zero
      exfalso
      simp [h_tail_empty, implementation_empty] at h_tail_zero
      simp [h_head_sum_zero, buckets_needed_zero] at h_head_zero
      have : 0 + 0 = 0 := by simp
      simp [h_head_zero, h_tail_zero] at h
      simp [h_tail_empty, implementation_empty] at h
      simp [h_head_sum_zero, buckets_needed_zero] at h
      have : head.sum > 0 := by
        have : head ≠ [] := by
          intro h_empty
          simp [h_empty] at h_head_sum_zero
          sorry
        sorry
      sorry
  · intro h
    simp [h, implementation_empty]

theorem correctness
(grid: List (List Nat))
(capacity: Nat)
: problem_spec implementation grid capacity := by
  exists implementation grid capacity
  constructor
  · rfl
  · intro h_binary h_uniform
    constructor
    · constructor
      · intro h_result_zero
        cases' grid with head tail
        · rfl
        · simp [implementation_cons] at h_result_zero
          have h_impl_tail_nonneg : implementation tail capacity ≥ 0 := implementation_nonneg tail capacity
          have h_buckets_nonneg : buckets_needed head.sum capacity ≥ 0 := Nat.zero_le _
          have h_buckets_zero : buckets_needed head.sum capacity = 0 := by omega
          have h_tail_zero : implementation tail capacity = 0 := by omega
          exfalso
          simp [buckets_needed] at h_buckets_zero
          have : head.sum / capacity + (if head.sum % capacity > 0 then 1 else 0) = 0 := h_buckets_zero
          by_cases h : head.sum % capacity > 0
          · simp [h] at this
            omega
          · simp [h] at this
            have h_div_zero : head.sum / capacity = 0 := this
            have h_sum_zero : head.sum = 0 := by
              have h_lt : head.sum < capacity := Nat.div_eq_zero_iff_lt.mp h_div_zero
              have h_mod_zero : head.sum % capacity = 0 := Nat.eq_zero_of_le_zero (le_of_not_gt h)
              exact Nat.eq_zero_of_zero_dvd ⟨h_mod_zero⟩ h_lt
            simp [h_sum_zero, buckets_needed_zero] at h_buckets_zero
            have : List.length (head :: tail) > 0 := Nat.zero_lt_succ _
            simp at this
      · intro h_empty
        simp [List.length_eq_zero] at h_empty
        simp [h_empty, implementation_empty]
    · intro h_nonempty
      cases' grid with head tail
      · simp at h_nonempty
      · simp [implementation_cons]
        simp [buckets_needed]
        ring