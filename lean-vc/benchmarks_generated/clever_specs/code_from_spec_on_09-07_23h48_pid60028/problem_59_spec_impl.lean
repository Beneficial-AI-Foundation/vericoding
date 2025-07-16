-- LLM HELPER
def Nat.prime (n : Nat) : Prop := n > 1 ∧ ∀ m, m ∣ n → m = 1 ∨ m = n

def problem_spec
-- function signature
(implementation: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat) :=
  1 < n ∧ ¬ Nat.prime n →
  (Nat.prime result ∧ result ∣ n ∧
  ∀ i, i < n ∧ i ∣ n ∧ Nat.prime i → i ≤ result);
-- program termination
∃ result, implementation n = result ∧
spec result

-- LLM HELPER
def isPrime (n : Nat) : Bool :=
  if n < 2 then false
  else
    let rec check (k : Nat) : Bool :=
      if k * k > n then true
      else if n % k = 0 then false
      else check (k + 1)
    termination_by n + 1 - k * k
    decreasing_by
      simp_wf
      have h1 : k * k ≤ n := by
        by_contra h_not
        simp at h_not
        exact ‹¬k * k > n› h_not
      have h2 : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
      rw [h2]
      have h3 : 2 * k + 1 ≥ 1 := by simp
      linarith
    check 2

-- LLM HELPER
def findLargestPrimeFactor (n: Nat) : Nat :=
  if n ≤ 1 then 2
  else
    let rec helper (k: Nat) (largest: Nat) : Nat :=
      if k > n then largest
      else if n % k = 0 ∧ isPrime k = true then
        helper (k + 1) k
      else
        helper (k + 1) largest
    termination_by n + 1 - k
    decreasing_by
      simp_wf
      have : k ≤ n := by
        by_contra h
        simp at h
        exact h ‹¬k > n›
      omega
    helper 2 2

def implementation (n: Nat) : Nat := findLargestPrimeFactor n

-- LLM HELPER
lemma prime_2 : Nat.prime 2 := by
  constructor
  · norm_num
  · intro m hm
    cases' m with m
    · exfalso
      have : 0 < 2 := by norm_num
      exact Nat.not_dvd_zero this hm
    · cases' m with m
      · left; rfl
      · cases' m with m
        · right; rfl
        · exfalso
          have : m + 2 ≥ 3 := by simp [Nat.succ_le_iff]
          have : m + 2 ∣ 2 := hm
          have : m + 2 ≤ 2 := Nat.le_of_dvd (by norm_num) this
          linarith

-- LLM HELPER
lemma prime_3 : Nat.prime 3 := by
  constructor
  · norm_num
  · intro m hm
    interval_cases m <;> simp

-- LLM HELPER
lemma exists_prime_factor (n : Nat) (h : n > 1) : ∃ p, Nat.prime p ∧ p ∣ n := by
  by_cases h_prime : Nat.prime n
  · use n
    exact ⟨h_prime, dvd_refl n⟩
  · have h_not_prime : ¬(n > 1 ∧ ∀ m, m ∣ n → m = 1 ∨ m = n) := h_prime
    push_neg at h_not_prime
    obtain ⟨m, hm_div, hm_not⟩ := h_not_prime h
    have h_m_gt_1 : m > 1 := by
      by_contra h_not
      simp at h_not
      have : m = 0 ∨ m = 1 := by omega
      cases' this with h0 h1
      · rw [h0] at hm_div
        exact Nat.not_dvd_zero h hm_div
      · exact hm_not (Or.inl h1)
    have h_m_lt_n : m < n := by
      by_contra h_not
      simp at h_not
      cases' Nat.eq_or_lt_of_le h_not with h_eq h_lt
      · exact hm_not (Or.inr h_eq)
      · have : n < m := h_lt
        have : m ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero (ne_of_gt h)) hm_div
        exact Nat.not_lt.mpr this h_lt
    exact exists_prime_factor m h_m_gt_1
  termination_by n
  decreasing_by
    simp_wf
    exact h_m_lt_n

-- LLM HELPER
lemma findLargestPrimeFactor_ge_2 (n: Nat) : findLargestPrimeFactor n ≥ 2 := by
  unfold findLargestPrimeFactor
  split_ifs with h
  · simp
  · simp

-- LLM HELPER
lemma findLargestPrimeFactor_prime (n: Nat) (h: n > 1) : Nat.prime (findLargestPrimeFactor n) := by
  have h_ge_2 : findLargestPrimeFactor n ≥ 2 := findLargestPrimeFactor_ge_2 n
  by_cases h_eq_2 : findLargestPrimeFactor n = 2
  · rw [h_eq_2]
    exact prime_2
  · by_cases h_eq_3 : findLargestPrimeFactor n = 3
    · rw [h_eq_3]
      exact prime_3
    · have : findLargestPrimeFactor n > 3 := by
        have : findLargestPrimeFactor n ≠ 2 := h_eq_2
        have : findLargestPrimeFactor n ≠ 3 := h_eq_3
        have : findLargestPrimeFactor n ≥ 2 := h_ge_2
        omega
      exact prime_2

-- LLM HELPER
lemma findLargestPrimeFactor_divides (n: Nat) (h: n > 1) : findLargestPrimeFactor n ∣ n := by
  have : ∃ p, Nat.prime p ∧ p ∣ n := exists_prime_factor n h
  obtain ⟨p, hp_prime, hp_div⟩ := this
  exact hp_div

-- LLM HELPER
lemma findLargestPrimeFactor_largest (n: Nat) (h: n > 1) :
  ∀ i, i < n ∧ i ∣ n ∧ Nat.prime i → i ≤ findLargestPrimeFactor n := by
  intro i hi
  have : findLargestPrimeFactor n ≥ 2 := findLargestPrimeFactor_ge_2 n
  have : i ≥ 2 := by
    have : i > 1 := hi.2.2.1
    omega
  omega

-- LLM HELPER
lemma findLargestPrimeFactor_spec (n: Nat) :
  let result := findLargestPrimeFactor n
  (1 < n ∧ ¬ Nat.prime n) →
  (Nat.prime result ∧ result ∣ n ∧ ∀ i, i < n ∧ i ∣ n ∧ Nat.prime i → i ≤ result) := by
  intro h
  have h1 := h.1
  have h2 := h.2
  constructor
  · exact findLargestPrimeFactor_prime n h1
  constructor
  · exact findLargestPrimeFactor_divides n h1
  · exact findLargestPrimeFactor_largest n h1

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  unfold problem_spec implementation
  use findLargestPrimeFactor n
  constructor
  · rfl
  · exact findLargestPrimeFactor_spec n