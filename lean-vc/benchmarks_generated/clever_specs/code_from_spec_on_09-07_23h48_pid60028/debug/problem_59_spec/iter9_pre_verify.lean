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
        by_contra h
        simp at h
        exact h ‹¬k * k > n›
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
      linarith
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
        · right; norm_num
          have : m + 2 ≥ 3 := by simp [Nat.succ_le_iff]
          have : m + 2 ∣ 2 := hm
          have : m + 2 ≤ 2 := Nat.le_of_dvd (by norm_num) this
          linarith

-- LLM HELPER  
lemma two_divides_even (n : Nat) : n % 2 = 0 → 2 ∣ n := by
  intro h
  exact Nat.dvd_iff_mod_eq_zero.mpr h

-- LLM HELPER
lemma exists_prime_factor_of_not_prime (n : Nat) (h1 : 1 < n) (h2 : ¬ Nat.prime n) :
  ∃ p, Nat.prime p ∧ p ∣ n := by
  have h_not_prime : ¬(n > 1 ∧ ∀ m, m ∣ n → m = 1 ∨ m = n) := h2
  push_neg at h_not_prime
  have h_gt_one : n > 1 := h1
  have h_exists_factor : ∃ m, m ∣ n ∧ m ≠ 1 ∧ m ≠ n := by
    have := h_not_prime h_gt_one
    obtain ⟨m, hm_div, hm_not⟩ := this
    use m
    constructor
    · exact hm_div
    · push_neg at hm_not
      exact hm_not
  obtain ⟨m, hm_div, hm_ne1, hm_nen⟩ := h_exists_factor
  by_cases h : n % 2 = 0
  · use 2
    constructor
    · exact prime_2
    · exact two_divides_even n h
  · use 2
    constructor
    · exact prime_2
    · exact hm_div

-- LLM HELPER
lemma findLargestPrimeFactor_works (n: Nat) (h1: 1 < n) (h2: ¬ Nat.prime n) :
  let result := findLargestPrimeFactor n
  Nat.prime result ∧ result ∣ n ∧ ∀ i, i < n ∧ i ∣ n ∧ Nat.prime i → i ≤ result := by
  unfold findLargestPrimeFactor
  simp [h1]
  constructor
  · exact prime_2
  constructor
  · have : ∃ p, Nat.prime p ∧ p ∣ n := exists_prime_factor_of_not_prime n h1 h2
    obtain ⟨p, hp_prime, hp_div⟩ := this
    exact hp_div
  · intro i hi
    have : i ≤ n := by
      by_contra h_not
      simp at h_not
      exact Nat.not_lt.mpr (Nat.le_of_lt h_not) hi.1
    have : findLargestPrimeFactor n ≥ 2 := by
      unfold findLargestPrimeFactor
      simp [h1]
    have : 2 ≤ n := Nat.succ_le_iff.mpr h1
    have : i ≤ n := this
    linarith

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  unfold problem_spec implementation
  use findLargestPrimeFactor n
  constructor
  · rfl
  · intro h
    have h1 := h.1
    have h2 := h.2
    exact findLargestPrimeFactor_works n h1 h2