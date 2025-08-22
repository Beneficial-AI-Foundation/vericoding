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
lemma implementation_zero_iff_empty (grid: List (List Nat)) (capacity: Nat) : 
  implementation grid capacity = 0 ↔ grid = [] := by
  constructor
  · intro h
    induction grid with
    | nil => rfl
    | cons head tail ih =>
      simp [implementation_cons] at h
      have h_buckets_nonneg : buckets_needed head.sum capacity ≥ 0 := Nat.zero_le _
      have h_tail_nonneg : implementation tail capacity ≥ 0 := implementation_nonneg tail capacity
      omega
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
      · intro h
        rw [implementation_zero_iff_empty] at h
        simp [h]
      · intro h
        rw [implementation_zero_iff_empty]
        simp [h]
    · intro h_nonempty
      cases' grid with head tail
      · simp at h_nonempty
      · simp [implementation_cons]
        simp [buckets_needed]
        ring