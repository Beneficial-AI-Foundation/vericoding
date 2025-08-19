def problem_spec
(implementation: Int → Int → Bool)
(x: Int) (n: Int) :=
let spec (result: Bool) :=
  result = true → exists k: Nat, x = n^k
∃ result, implementation x n = result ∧
spec result

-- LLM HELPER
def isPowerOfHelper (x: Int) (n: Int) (fuel: Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    if x = 1 then true
    else if n = 0 then false
    else if n = 1 then x = 1
    else if n = -1 then x = 1 || x = -1
    else if x % n ≠ 0 then false
    else isPowerOfHelper (x / n) n fuel'

def implementation (x: Int) (n: Int) : Bool := 
  if x = 1 then true
  else if n = 0 then false
  else if n = 1 then x = 1
  else if n = -1 then x = 1 || x = -1
  else if x > 0 && n > 1 then isPowerOfHelper x n (Int.natAbs x + 1)
  else if x < 0 && n < -1 then isPowerOfHelper x n (Int.natAbs x + 1)
  else false

-- LLM HELPER
lemma power_zero_eq_one (n: Int) : n^0 = 1 := by simp [pow_zero]

-- LLM HELPER
lemma power_one_eq_self (n: Int) : n^1 = n := by simp [pow_one]

-- LLM HELPER
lemma helper_sound (x n: Int) (fuel: Nat) (h: isPowerOfHelper x n fuel = true) :
  ∃ k: Nat, x = n^k := by
  induction fuel generalizing x with
  | zero => simp [isPowerOfHelper] at h
  | succ fuel' ih =>
    simp [isPowerOfHelper] at h
    by_cases h1: x = 1
    · simp [h1] at h
      use 0
      simp [power_zero_eq_one]
    · simp [h1] at h
      by_cases h2: n = 0
      · simp [h2] at h
      · simp [h2] at h
        by_cases h3: n = 1
        · simp [h3] at h
          use 1
          simp [power_one_eq_self, h]
        · simp [h3] at h
          by_cases h4: n = -1
          · simp [h4] at h
            cases' h with h5 h6
            · use 0; simp [power_zero_eq_one, h5]
            · use 1; simp [power_one_eq_self, h6]
          · simp [h4] at h
            by_cases h5: x % n ≠ 0
            · simp [h5] at h
            · simp [h5] at h
              have h6 := ih (x / n) h
              obtain ⟨k, hk⟩ := h6
              use k + 1
              simp [pow_succ, hk]
              have h7 : x % n = 0 := by simp [h5]
              have h8 : x = x / n * n := Int.div_mul_cancel x h7
              rw [h8, hk]
              ring

-- LLM HELPER
lemma implementation_sound (x n: Int) (h: implementation x n = true) :
  ∃ k: Nat, x = n^k := by
  unfold implementation at h
  by_cases h1: x = 1
  · simp [h1] at h
    use 0
    simp [power_zero_eq_one]
  · simp [h1] at h
    by_cases h2: n = 0
    · simp [h2] at h
    · simp [h2] at h
      by_cases h3: n = 1
      · simp [h3] at h
        use 1
        simp [power_one_eq_self, h]
      · simp [h3] at h
        by_cases h4: n = -1
        · simp [h4] at h
          cases' h with h5 h6
          · use 0; simp [power_zero_eq_one, h5]
          · use 1; simp [power_one_eq_self, h6]
        · simp [h4] at h
          by_cases h5: x > 0 ∧ n > 1
          · simp [h5] at h
            exact helper_sound x n (Int.natAbs x + 1) h
          · simp [h5] at h
            by_cases h6: x < 0 ∧ n < -1
            · simp [h6] at h
              exact helper_sound x n (Int.natAbs x + 1) h
            · simp [h6] at h

theorem correctness
(x: Int) (n: Int)
: problem_spec implementation x n := by
  unfold problem_spec
  use implementation x n
  constructor
  · rfl
  · intro h
    exact implementation_sound x n h