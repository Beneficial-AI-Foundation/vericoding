def problem_spec
-- function signature
(implementation: List Nat → Nat)
-- inputs
(lst: List Nat) :=
-- spec
let spec (result : Nat) :=
  lst.any (fun num => Nat.Prime num) →
    result > 0 ∧ ∃ i, i < lst.length ∧ Prime (lst.get! i) ∧
    (∀ j, j < lst.length ∧ Prime (lst.get! j) → lst.get! i ≤ lst.get! j) ∧
    result = (Nat.digits 10 (lst.get! i)).sum
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

-- LLM HELPER
def findMinPrime (lst: List Nat) : Option Nat :=
  let primes := lst.filter Nat.Prime
  if primes.isEmpty then none
  else some (primes.minimum?)

-- LLM HELPER
def digitSum (n: Nat) : Nat := (Nat.digits 10 n).sum

def implementation (lst: List Nat) : Nat :=
  match lst.filter Nat.Prime with
  | [] => 0
  | primes => digitSum (primes.minimum?)

-- LLM HELPER
lemma digits_sum_pos (n: Nat) (h: n > 0) : (Nat.digits 10 n).sum > 0 := by
  cases' n with n
  · contradiction
  · simp [Nat.digits]
    by_cases h : n.succ < 10
    · simp [Nat.digits, h]
      exact Nat.zero_lt_succ n
    · simp [Nat.digits, h]
      exact Nat.add_pos_left (Nat.mod_pos (Nat.succ n) (by norm_num)) _

-- LLM HELPER
lemma prime_pos (p: Nat) (h: Nat.Prime p) : p > 0 := Nat.Prime.pos h

-- LLM HELPER
lemma filter_prime_any (lst: List Nat) : lst.any Nat.Prime = !(lst.filter Nat.Prime).isEmpty := by
  simp [List.any_eq_true, List.isEmpty_iff_eq_nil]
  constructor
  · intro h
    by_contra h_empty
    have : lst.filter Nat.Prime = [] := h_empty
    simp [List.filter_eq_nil] at this
    exact this h
  · intro h
    obtain ⟨x, hx_mem, hx_prime⟩ := List.exists_mem_of_ne_nil h
    simp [List.mem_filter] at hx_mem
    exact ⟨x, hx_mem.1, hx_mem.2⟩

-- LLM HELPER
lemma get_mem_of_lt (lst: List Nat) (i: Nat) (h: i < lst.length) : lst.get! i ∈ lst := by
  exact List.get!_mem lst i h

-- LLM HELPER
lemma minimum_mem_of_nonempty (lst: List Nat) (h: lst ≠ []) : lst.minimum? ∈ lst := by
  simp [List.minimum?]
  exact List.min_mem lst h

-- LLM HELPER
lemma minimum_le_all (lst: List Nat) (x: Nat) (h: x ∈ lst) : lst.minimum? ≤ x := by
  simp [List.minimum?]
  exact List.min_le_of_mem h

theorem correctness
(lst: List Nat)
: problem_spec implementation lst := by
  simp [problem_spec]
  use implementation lst
  constructor
  · rfl
  · intro h_any
    simp [implementation]
    rw [filter_prime_any] at h_any
    simp at h_any
    cases' h_filter : lst.filter Nat.Prime with
    | nil => contradiction
    | cons head tail =>
      simp [List.minimum?]
      have h_min_prime : Nat.Prime (head :: tail).minimum? := by
        have h_min_mem : (head :: tail).minimum? ∈ head :: tail := minimum_mem_of_nonempty _ (by simp)
        have h_all_prime : ∀ x ∈ head :: tail, Nat.Prime x := by
          intro x hx
          have : x ∈ lst.filter Nat.Prime := by rwa [h_filter]
          exact List.mem_filter.mp this |>.2
        exact h_all_prime _ h_min_mem
      have h_min_pos : (head :: tail).minimum? > 0 := prime_pos _ h_min_prime
      constructor
      · exact digits_sum_pos _ h_min_pos
      · obtain ⟨i, hi_lt, hi_eq⟩ := List.indexOf_lt_length.mpr (by
          have : (head :: tail).minimum? ∈ head :: tail := minimum_mem_of_nonempty _ (by simp)
          rw [h_filter] at this
          exact List.mem_filter.mp this |>.1)
        use i
        constructor
        · exact hi_lt
        · constructor
          · have : lst.get! i ∈ lst.filter Nat.Prime := by
              rw [List.get!_mem_iff_lt]
              exact hi_lt
            exact List.mem_filter.mp this |>.2
          · constructor
            · intro j hj_lt hj_prime
              have : lst.get! j ∈ lst.filter Nat.Prime := by
                simp [List.mem_filter]
                exact ⟨get_mem_of_lt _ _ hj_lt, hj_prime⟩
              rw [h_filter] at this
              have : lst.get! i ∈ head :: tail := by
                simp [List.mem_filter] at *
                have : lst.get! i ∈ lst.filter Nat.Prime := by
                  simp [List.mem_filter]
                  exact ⟨get_mem_of_lt _ _ hi_lt, List.mem_filter.mp (by rw [← h_filter]; exact this) |>.2⟩
                rw [h_filter] at this
                exact this
              exact minimum_le_all _ _ this
            · rfl