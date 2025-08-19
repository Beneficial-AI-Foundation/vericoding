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
def wells_needed (water_count : Nat) (capacity : Nat) : Nat :=
  if capacity = 0 then 0 else (water_count + capacity - 1) / capacity

def implementation (grid: List (List Nat)) (capacity: Nat) : Nat :=
  match grid with
  | [] => 0
  | row :: rest => wells_needed row.sum capacity + implementation rest capacity

-- LLM HELPER
lemma wells_needed_correct (water_count capacity : Nat) (h : capacity > 0) :
  wells_needed water_count capacity = water_count / capacity + (if water_count % capacity > 0 then 1 else 0) := by
  simp [wells_needed]
  split
  · contradiction
  · rw [Nat.add_div_right _ h]
    congr
    by_cases hmod : water_count % capacity > 0
    · simp [hmod]
      rw [Nat.add_div_of_dvd_right]
      · simp
      · exact Nat.dvd_refl capacity
    · simp [hmod]
      have : water_count % capacity = 0 := by
        rw [Nat.not_lt] at hmod
        exact Nat.eq_zero_of_le_zero hmod
      rw [this]
      simp

-- LLM HELPER
lemma implementation_recursive (grid : List (List Nat)) (capacity : Nat) :
  grid.length > 0 →
  implementation grid capacity = wells_needed grid.head!.sum capacity + implementation grid.tail! capacity := by
  intro h
  cases' grid with head tail
  · simp at h
  · simp [implementation]

-- LLM HELPER
lemma list_length_pos_iff_nonempty (l : List α) : l.length > 0 ↔ l ≠ [] := by
  constructor
  · intro h
    intro h_empty
    rw [h_empty] at h
    simp at h
  · intro h
    cases' l with head tail
    · contradiction
    · simp

theorem correctness
(grid: List (List Nat))
(capacity: Nat)
: problem_spec implementation grid capacity := by
  simp [problem_spec]
  use implementation grid capacity
  constructor
  · rfl
  · intro h_binary h_uniform
    constructor
    · constructor
      · intro h_zero
        have h_empty : grid = [] := by
          cases' grid with head tail
          · rfl
          · simp [implementation] at h_zero
        exact h_empty
      · intro h_empty
        rw [h_empty]
        simp [implementation]
    · intro h_pos
      cases' grid with head tail
      · simp at h_pos
      · simp [implementation]
        by_cases h_cap : capacity = 0
        · simp [h_cap, wells_needed]
        · push_neg at h_cap
          have h_cap_pos : capacity > 0 := Nat.pos_of_ne_zero h_cap
          rw [wells_needed_correct head.sum capacity h_cap_pos]
          ring