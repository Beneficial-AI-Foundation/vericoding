def problem_spec
-- function signature
(implementation: List Nat → Nat)
-- inputs
(lst: List Nat) :=
-- spec
let spec (result : Nat) :=
  lst.any (fun num => Nat.prime num) →
    result > 0 ∧ ∃ i, i < lst.length ∧ Nat.prime (lst[i]!) ∧
    (∀ j, j < lst.length ∧ Nat.prime (lst[j]!) → lst[i]! ≤ lst[j]!) ∧
    result = (Nat.digits 10 (lst[i]!)).sum
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

-- LLM HELPER
def digitSum (n: Nat) : Nat := (Nat.digits 10 n).sum

-- LLM HELPER
def List.minimum? (lst: List Nat) : Option Nat :=
  match lst with
  | [] => none
  | h :: t => some (t.foldl min h)

-- LLM HELPER
def List.minimum (lst: List Nat) : Nat :=
  match lst with
  | [] => 0
  | h :: t => t.foldl min h

def implementation (lst: List Nat) : Nat :=
  let primes := lst.filter Nat.prime
  if primes.isEmpty then 0
  else digitSum (primes.minimum)

-- LLM HELPER
lemma digits_sum_pos (n: Nat) (h: n > 0) : (Nat.digits 10 n).sum > 0 := by
  rw [Nat.digits_sum]
  exact Nat.sum_pos_of_pos n h

-- LLM HELPER
lemma prime_pos (p: Nat) (h: Nat.prime p) : p > 0 := Nat.prime.pos h

-- LLM HELPER
lemma filter_prime_any (lst: List Nat) : lst.any Nat.prime = !(lst.filter Nat.prime).isEmpty := by
  simp [List.any_eq_true, List.isEmpty_iff_eq_nil]
  constructor
  · intro h
    by_contra h_empty
    have : lst.filter Nat.prime = [] := h_empty
    simp [List.filter_eq_nil] at this
    exact this h
  · intro h
    obtain ⟨x, hx_mem, hx_prime⟩ := List.exists_mem_of_ne_nil h
    simp [List.mem_filter] at hx_mem
    exact ⟨x, hx_mem.1, hx_mem.2⟩

-- LLM HELPER
lemma minimum_mem_of_nonempty (lst: List Nat) (h: lst ≠ []) : lst.minimum ∈ lst := by
  cases lst with
  | nil => contradiction
  | cons head tail =>
    simp [List.minimum]
    apply List.foldl_mem_of_mem
    simp

-- LLM HELPER
lemma minimum_le_all (lst: List Nat) (x: Nat) (h: x ∈ lst) : lst.minimum ≤ x := by
  cases lst with
  | nil => simp at h
  | cons head tail =>
    simp [List.minimum]
    induction tail generalizing head with
    | nil => simp; exact le_refl _
    | cons h t ih =>
      simp [List.foldl]
      cases' le_total head h with h1 h2
      · simp [min_def, h1]
        exact ih
      · simp [min_def, h2]
        exact ih

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
    have h_nonempty : lst.filter Nat.prime ≠ [] := h_any
    simp [List.isEmpty_iff_eq_nil] at h_nonempty
    let primes := lst.filter Nat.prime
    have h_min_prime : Nat.prime primes.minimum := by
      have h_min_mem : primes.minimum ∈ primes := minimum_mem_of_nonempty primes h_nonempty
      have h_all_prime : ∀ x ∈ primes, Nat.prime x := by
        intro x hx
        exact List.mem_filter.mp hx |>.2
      exact h_all_prime _ h_min_mem
    have h_min_pos : primes.minimum > 0 := prime_pos _ h_min_prime
    constructor
    · exact digits_sum_pos _ h_min_pos
    · have h_min_mem_orig : primes.minimum ∈ lst := by
        have : primes.minimum ∈ primes := minimum_mem_of_nonempty primes h_nonempty
        exact List.mem_filter.mp this |>.1
      obtain ⟨i, hi_lt, hi_eq⟩ := List.mem_iff_get.mp h_min_mem_orig
      use i
      constructor
      · exact hi_lt
      · constructor
        · rw [← hi_eq]
          exact h_min_prime
        · constructor
          · intro j hj_lt hj_prime
            rw [← hi_eq]
            have : lst[j]! ∈ primes := by
              simp [List.mem_filter]
              exact ⟨List.get_mem _ _ hj_lt, hj_prime⟩
            exact minimum_le_all _ _ this
          · rw [← hi_eq]
            rfl