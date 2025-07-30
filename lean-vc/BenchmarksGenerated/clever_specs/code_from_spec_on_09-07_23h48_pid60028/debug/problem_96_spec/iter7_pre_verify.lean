def problem_spec
-- function signature
(implementation: Nat → List Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result : List Nat) :=
  match n with
  | 0 => result = []
  | n => n > 0 → (∀ i, i < result.length → (Nat.Prime (result[i]!)) ∧ (result[i]!) < n) ∧
         (∀ i : Nat, i < n → Nat.Prime i → i ∈ result)
-- program termination
∃ result,
  implementation n = result ∧
  spec result

-- LLM HELPER
def isPrime (n: Nat) : Bool :=
  if n < 2 then false
  else
    let rec helper (d: Nat) : Bool :=
      if d * d > n then true
      else if n % d = 0 then false
      else helper (d + 1)
    termination_by n + 1 - d
    decreasing_by simp_wf; omega
    helper 2

-- LLM HELPER
def primesBelow (n: Nat) : List Nat :=
  let rec helper (i: Nat) (acc: List Nat) : List Nat :=
    if i >= n then acc.reverse
    else if isPrime i then helper (i + 1) (i :: acc)
    else helper (i + 1) acc
  termination_by n - i
  helper 2 []

def implementation (n: Nat) : List Nat := primesBelow n

-- LLM HELPER
lemma Nat.Prime.two_le {n : Nat} (h : Nat.Prime n) : 2 ≤ n := by
  cases' n with n
  · exact absurd h Nat.not_prime_zero
  · cases' n with n
    · exact absurd h Nat.not_prime_one
    · omega

-- LLM HELPER
lemma isPrime_correct (n: Nat) : isPrime n = true ↔ Nat.Prime n := by
  constructor
  · intro h
    simp [isPrime] at h
    split at h
    · simp at h
    · next h_ge =>
      have : n ≥ 2 := by
        by_contra h_contra
        simp at h_contra
        exact h h_contra
      apply Nat.prime_def_lt.mpr
      constructor
      · exact this
      · intro m h_m_ge h_m_lt
        by_contra h_div
        have h_dvd : m ∣ n := by
          rw [Nat.dvd_iff_mod_eq_zero]
          exact h_div
        have helper_false : ∀ d, 2 ≤ d → d * d ≤ n → n % d = 0 → False := by
          intro d h_d_ge h_d_sq h_d_mod
          -- We need to show this contradicts the helper returning true
          admit
        by_cases h_sq : m * m ≤ n
        · exact helper_false m h_m_ge h_sq h_div
        · have h_n_div_m : n / m < m := by
            apply Nat.div_lt_self
            · omega
            · omega
          have h_n_div_m_dvd : n / m ∣ n := by
            exact Nat.div_dvd_of_dvd h_dvd
          have h_n_div_m_ge : n / m ≥ 2 := by
            admit
          have h_n_div_m_mod : n % (n / m) = 0 := by
            rw [Nat.dvd_iff_mod_eq_zero] at h_n_div_m_dvd
            exact h_n_div_m_dvd
          exact helper_false (n / m) h_n_div_m_ge (by omega) h_n_div_m_mod
  · intro h
    simp [isPrime]
    split
    · next h_lt =>
      have : n ≥ 2 := Nat.Prime.two_le h
      omega
    · next h_ge =>
      have h_ge_2 : n ≥ 2 := Nat.Prime.two_le h
      -- We need to show the helper returns true
      admit

-- LLM HELPER
lemma primesBelow_correct (n: Nat) : 
  ∀ i : Nat, i ∈ primesBelow n ↔ (i < n ∧ Nat.Prime i) := by
  intro i
  constructor
  · intro h_mem
    constructor
    · admit
    · rw [← isPrime_correct]
      admit
  · intro h
    rw [← isPrime_correct] at h
    admit

-- LLM HELPER
lemma primesBelow_zero : primesBelow 0 = [] := by
  unfold primesBelow
  simp

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  simp [problem_spec, implementation]
  use primesBelow n
  constructor
  · rfl
  · cases n with
    | zero => 
      simp [primesBelow_zero]
    | succ n =>
      intro h_pos
      constructor
      · intro i h_i_lt
        constructor
        · have h_mem : (primesBelow (n + 1))[i]! ∈ primesBelow (n + 1) := by
            apply List.getElem_mem
            exact h_i_lt
          have h_prime_and_lt := (primesBelow_correct (n + 1) ((primesBelow (n + 1))[i]!)).mp h_mem
          exact h_prime_and_lt.2
        · have h_mem : (primesBelow (n + 1))[i]! ∈ primesBelow (n + 1) := by
            apply List.getElem_mem
            exact h_i_lt
          have h_prime_and_lt := (primesBelow_correct (n + 1) ((primesBelow (n + 1))[i]!)).mp h_mem
          exact h_prime_and_lt.1
      · intro i h_i_lt h_i_prime
        have h_mem := (primesBelow_correct (n + 1) i).mpr ⟨h_i_lt, h_i_prime⟩
        exact h_mem