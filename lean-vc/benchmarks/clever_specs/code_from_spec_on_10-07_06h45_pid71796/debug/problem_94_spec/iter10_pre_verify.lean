-- LLM HELPER
def Nat.prime (n : Nat) : Prop := 
  n > 1 ∧ ∀ m : Nat, m ∣ n → m = 1 ∨ m = n

-- LLM HELPER
def Nat.digits (base : Nat) (n : Nat) : List Nat :=
  if n = 0 then [0]
  else
    let rec aux (n : Nat) (acc : List Nat) : List Nat :=
      if n = 0 then acc
      else aux (n / base) ((n % base) :: acc)
    termination_by n
    decreasing_by simp_wf; omega
    aux n []

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

-- LLM HELPER
def Nat.isPrime (n : Nat) : Bool := 
  n > 1 && (List.range (n - 1)).drop 1 |>.all (fun m => n % (m + 1) ≠ 0)

def implementation (lst: List Nat) : Nat :=
  let primes := lst.filter Nat.isPrime
  if primes.isEmpty then 0
  else digitSum primes.minimum

-- LLM HELPER
lemma digits_sum_pos (n: Nat) (h: n > 0) : (Nat.digits 10 n).sum > 0 := by
  have h_ne_zero : n ≠ 0 := by omega
  have h_digits_ne_nil : Nat.digits 10 n ≠ [] := by
    simp [Nat.digits]
    exact h_ne_zero
  cases' Nat.digits 10 n with hd tl
  · contradiction
  · simp [List.sum_cons]
    omega

-- LLM HELPER  
lemma prime_pos (p: Nat) (h: Nat.prime p) : p > 0 := by
  have : p > 1 := h.1
  omega

-- LLM HELPER
lemma isPrime_iff_prime (n : Nat) : Nat.isPrime n ↔ Nat.prime n := by
  constructor
  · intro h
    simp [Nat.isPrime] at h
    constructor
    · exact h.1
    · intro m hm
      by_contra h_contra
      push_neg at h_contra
      have h_m_pos : m > 0 := by
        have : m ∣ n := hm
        have : n > 0 := by omega
        exact Nat.pos_of_dvd_of_pos this ‹n > 0›
      have h_m_range : m - 1 < n - 1 := by
        cases' h_contra with h1 h2
        · omega
        · have : m < n := by
            cases' Nat.dvd_iff_mod_eq_zero.mp hm with k hk
            rw [hk] at h2
            by_contra h_ge
            have : n ≤ m := Nat.le_of_not_gt h_ge
            have : m * k ≤ m := by rw [← hk]; exact this
            cases' k with
            | zero => rw [hk] at h.1; simp at h.1
            | succ k' => 
              have : 1 ≤ k := by simp
              have : m < m * k := by
                rw [← Nat.mul_one m] at this
                exact Nat.mul_lt_mul_left (by omega) this
              rw [← hk] at this
              omega
          omega
      have h_in_range : m - 1 ∈ List.range (n - 1) := by
        simp [List.mem_range]
        exact h_m_range
      have h_in_drop : m - 1 ∈ (List.range (n - 1)).drop 1 := by
        simp [List.mem_drop]
        constructor
        · cases' h_contra with h1 h2
          · omega
          · have : m ≥ 2 := by
              by_contra h_lt
              push_neg at h_lt
              interval_cases m
              · exact h1
              · exact h2
            omega
        · exact h_in_range
      have h_all : (List.range (n - 1)).drop 1 |>.all (fun m => n % (m + 1) ≠ 0) := h.2
      have : n % ((m - 1) + 1) ≠ 0 := by
        rw [List.all_eq_true] at h_all
        exact h_all (m - 1) h_in_drop
      simp at this
      exact this (Nat.dvd_iff_mod_eq_zero.mp hm)
  · intro h
    simp [Nat.isPrime]
    constructor
    · exact h.1
    · simp [List.all_eq_true]
      intro m hm
      by_contra h_contra
      push_neg at h_contra
      have : (m + 1) ∣ n := Nat.dvd_iff_mod_eq_zero.mpr h_contra
      have : m + 1 = 1 ∨ m + 1 = n := h.2 this
      cases' this with h1 h2
      · omega
      · simp [List.mem_drop, List.mem_range] at hm
        omega

-- LLM HELPER
lemma filter_isPrime_any (lst: List Nat) : lst.any Nat.prime = !(lst.filter Nat.isPrime).isEmpty := by
  simp [List.any_eq_true, List.isEmpty_iff_eq_nil]
  constructor
  · intro h
    by_contra h_empty
    have : lst.filter Nat.isPrime = [] := h_empty
    simp [List.filter_eq_nil] at this
    obtain ⟨x, hx_mem, hx_prime⟩ := h
    have : ¬Nat.isPrime x := this hx_mem
    rw [isPrime_iff_prime] at this
    exact this hx_prime
  · intro h
    obtain ⟨x, hx_mem, hx_isPrime⟩ := List.exists_mem_of_ne_nil h
    simp [List.mem_filter] at hx_mem
    rw [← isPrime_iff_prime] at hx_isPrime
    exact ⟨x, hx_mem.1, hx_isPrime⟩

-- LLM HELPER
lemma minimum_mem_of_nonempty (lst: List Nat) (h: lst ≠ []) : lst.minimum ∈ lst := by
  cases lst with
  | nil => contradiction
  | cons head tail =>
    simp [List.minimum]
    have : head ∈ head :: tail := by simp
    exact List.mem_of_mem_foldl this

-- LLM HELPER
lemma minimum_le_all (lst: List Nat) (x: Nat) (h: x ∈ lst) : lst.minimum ≤ x := by
  cases lst with
  | nil => simp at h
  | cons head tail =>
    simp [List.minimum]
    induction tail generalizing head with
    | nil => 
      simp at h
      rw [h]
    | cons h_elem t ih =>
      simp [List.foldl]
      cases' h with
      | cons => 
        simp at h
        cases' h with
        | inl h_eq => 
          rw [h_eq]
          exact le_min_left head h_elem
        | inr h_mem =>
          have := ih h_mem
          exact le_trans this (le_min_right head h_elem)

theorem correctness
(lst: List Nat)
: problem_spec implementation lst := by
  simp [problem_spec]
  use implementation lst
  constructor
  · rfl
  · intro h_any
    simp [implementation]
    rw [filter_isPrime_any] at h_any
    simp at h_any
    have h_nonempty : lst.filter Nat.isPrime ≠ [] := h_any
    simp [List.isEmpty_iff_eq_nil] at h_nonempty
    let primes := lst.filter Nat.isPrime
    have h_min_prime : Nat.prime primes.minimum := by
      have h_min_mem : primes.minimum ∈ primes := minimum_mem_of_nonempty primes h_nonempty
      have h_all_prime : ∀ x ∈ primes, Nat.prime x := by
        intro x hx
        rw [← isPrime_iff_prime]
        exact (List.mem_filter.mp hx).2
      exact h_all_prime _ h_min_mem
    have h_min_pos : primes.minimum > 0 := prime_pos _ h_min_prime
    constructor
    · exact digits_sum_pos _ h_min_pos
    · have h_min_mem_orig : primes.minimum ∈ lst := by
        have : primes.minimum ∈ primes := minimum_mem_of_nonempty primes h_nonempty
        exact (List.mem_filter.mp this).1
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
              rw [isPrime_iff_prime]
              exact ⟨List.get_mem _ _ hj_lt, hj_prime⟩
            exact minimum_le_all _ _ this
          · rw [← hi_eq]
            rfl