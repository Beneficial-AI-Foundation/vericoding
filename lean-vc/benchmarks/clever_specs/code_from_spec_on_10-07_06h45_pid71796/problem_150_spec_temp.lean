def problem_spec
-- function signature
(impl: Int → Int → Int → Int)
-- inputs
(n x y: Int) :=
-- spec
let spec (result: Int) :=
(result = x ↔ Nat.Prime n.toNat) ∧
(result = y ↔ (¬ Nat.Prime n.toNat ∨ n ≤ 1))
-- program terminates
∃ result, impl n x y = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def isPrime (n : Int) : Bool :=
  if n ≤ 1 then false
  else
    let rec check (k : Nat) : Bool :=
      if k * k > n.toNat then true
      else if n.toNat % k = 0 then false
      else check (k + 1)
    termination_by n.toNat + 1 - k
    decreasing_by simp_wf; omega
    check 2

def implementation (n x y: Int) : Int := 
  if isPrime n then x else y

-- LLM HELPER
lemma isPrime_correct (n : Int) : isPrime n = true ↔ Nat.Prime n.toNat := by
  simp [isPrime]
  split_ifs with h
  · simp
    constructor
    · intro
      exfalso
      have : ¬ Nat.Prime n.toNat := by
        rw [Nat.Prime]
        simp
        left
        omega
      contradiction
    · intro hp
      exfalso
      have : n.toNat ≥ 2 := by
        rw [Nat.Prime] at hp
        omega
      have : n ≥ 2 := by
        have : n.toNat ≥ 2 := this
        cases' n with n n
        · simp at this
          omega
        · simp at this
          omega
      omega
  · simp
    constructor
    · intro hcheck
      have n_pos : n > 1 := by omega
      rw [Nat.Prime]
      constructor
      · omega
      · intro d hdiv hd_ge_2
        by_contra hcontra
        simp at hcontra
        have d_lt_n : d < n.toNat := by
          by_contra hge
          simp at hge
          cases' hge with hge heq
          · have : n.toNat < d := hge
            have : d ∣ n.toNat := hdiv
            rw [Nat.dvd_iff_mod_eq_zero] at this
            have : n.toNat % d = 0 := this
            have : n.toNat < d := hge
            have : n.toNat % d = n.toNat := Nat.mod_eq_of_lt this
            rw [this] at this
            omega
          · rw [heq] at hdiv
            have : n.toNat ∣ n.toNat := hdiv
            simp at this
        have : d * d ≤ n.toNat := by
          rw [hcontra]
          exact Nat.le_refl _
        have : ¬ (d * d > n.toNat) := by omega
        have h_check : check d = false := by
          rw [check]
          simp [this]
          rw [Nat.dvd_iff_mod_eq_zero] at hdiv
          simp [hdiv]
        have : check 2 = false := by
          have : 2 ≤ d := hd_ge_2
          induction' d, this using Nat.le_induction with d hd ih
          · exact h_check
          · exact ih
        simp [this] at hcheck
    · intro hp
      have n_pos : n > 1 := by
        rw [Nat.Prime] at hp
        omega
      have : ∀ d, 2 ≤ d → d * d ≤ n.toNat → ¬ (d ∣ n.toNat) := by
        intro d hd_ge_2 hd_sq_le hdiv
        have : d < n.toNat := by
          by_contra hge
          simp at hge
          cases' hge with hge heq
          · have : n.toNat < d := hge
            have : d ∣ n.toNat := hdiv
            rw [Nat.dvd_iff_mod_eq_zero] at this
            have : n.toNat % d = 0 := this
            have : n.toNat < d := hge
            have : n.toNat % d = n.toNat := Nat.mod_eq_of_lt this
            rw [this] at this
            omega
          · rw [heq] at hdiv
            have : n.toNat ∣ n.toNat := hdiv
            simp at this
        rw [Nat.Prime] at hp
        exact hp.2 d hdiv hd_ge_2 this
      have : check 2 = true := by
        induction' n.toNat using Nat.strong_induction_on with n ih
        simp [check]
        split_ifs with h1 h2
        · rfl
        · exfalso
          have : 2 ∣ n := by
            rw [Nat.dvd_iff_mod_eq_zero]
            exact h2
          have : 2 ≥ 2 := by omega
          have : 2 * 2 ≤ n := by
            by_contra hcontra
            simp at hcontra
            have : 2 * 2 > n := hcontra
            exact h1 this
          exact this _ this this this
        · simp [check]
          sorry
      simp [this]

-- LLM HELPER  
lemma isPrime_false (n : Int) : isPrime n = false ↔ (¬ Nat.Prime n.toNat ∨ n ≤ 1) := by
  constructor
  · intro h
    by_contra hcontra
    simp at hcontra
    have : isPrime n = true := by
      rw [isPrime_correct]
      exact hcontra.1
    rw [this] at h
    simp at h
  · intro h
    by_contra hcontra
    have : isPrime n = true := by simp at hcontra; exact hcontra
    rw [isPrime_correct] at this
    cases h with
    | inl h1 => exact h1 this
    | inr h2 => 
      have : n > 1 := by
        rw [Nat.Prime] at this
        omega
      omega

theorem correctness
(n x y: Int)
: problem_spec implementation n x y := by
  simp [problem_spec, implementation]
  use (if isPrime n then x else y)
  constructor
  · rfl
  · constructor
    · by_cases h : isPrime n
      · simp [h]
        constructor
        · intro
          rw [isPrime_correct] at h
          exact h
        · intro hp
          by_contra hcontra
          simp at hcontra
          have : isPrime n = false := hcontra
          rw [this] at h
          simp at h
      · simp [h]
        constructor
        · intro hcontra
          simp at hcontra
        · intro hp
          exfalso
          have : isPrime n = true := by
            rw [isPrime_correct]
            exact hp
          rw [this] at h
          simp at h
    · by_cases h : isPrime n
      · simp [h]
        constructor
        · intro hcontra
          simp at hcontra
        · intro hp
          exfalso
          rw [isPrime_correct] at h
          exact hp h
      · simp [h]
        constructor
        · intro
          rw [isPrime_false] at h
          exact h
        · intro hp
          by_contra hcontra
          simp at hcontra
          have : isPrime n = true := hcontra
          rw [this] at h
          simp at h