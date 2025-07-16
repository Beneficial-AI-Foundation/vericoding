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
        · simp [implementation_empty]
        · simp [implementation_cons] at h_result_zero
          have h_buckets_zero : buckets_needed head.sum capacity = 0 := by
            have h_impl_tail_nonneg : implementation tail capacity ≥ 0 := by
              induction tail with
              | nil => simp [implementation_empty]
              | cons h t ih => 
                simp [implementation_cons]
                apply Nat.add_pos_left
                simp [buckets_needed]
                cases' h_bucket : h.sum / capacity + (if h.sum % capacity > 0 then 1 else 0) with
                | zero => contradiction
                | succ _ => simp
            omega
          have h_water_zero : head.sum = 0 := by
            simp [buckets_needed] at h_buckets_zero
            by_cases h : head.sum % capacity > 0
            · simp [h] at h_buckets_zero
              have : head.sum / capacity + 1 = 0 := h_buckets_zero
              omega
            · simp [h] at h_buckets_zero
              have : head.sum / capacity = 0 := h_buckets_zero
              have : head.sum < capacity := Nat.div_eq_zero_iff_lt.mp this
              have : head.sum % capacity = 0 := by
                simp [not_lt] at h
                exact Nat.eq_zero_of_le_zero h
              exact Nat.dvd_iff_mod_eq_zero.mp ⟨this, rfl⟩
          simp [List.length_cons]
      · intro h_empty
        simp [List.length_eq_zero] at h_empty
        simp [h_empty, implementation_empty]
    · intro h_nonempty
      cases' grid with head tail
      · simp at h_nonempty
      · simp [implementation_cons]
        simp [buckets_needed]
        ring