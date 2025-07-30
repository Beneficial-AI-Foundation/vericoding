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
        simp [isPrime] at h
        split at h
        · simp at h
        · next h_ge2 =>
          have : isPrime.helper n 2 = true := h
          have h_helper : ∀ d, d * d ≤ n → d ≥ 2 → isPrime.helper n d = true → (∀ k, 2 ≤ k → k < d → n % k ≠ 0) := by
            intro d h_d_sq h_d_ge2 h_helper_true k h_k_ge2 h_k_lt
            have : n % k ≠ 0 := by
              induction d using Nat.strong_induction_on with
              | h d' ih =>
                simp [isPrime.helper] at h_helper_true
                split at h_helper_true
                · next h_sq_gt =>
                  have : k * k ≤ n := by
                    have : k < d' := h_k_lt
                    have : k * k < d' * d' := by
                      apply Nat.mul_lt_mul
                      exact h_k_lt
                      exact h_k_lt
                    omega
                  have : k * k > n := by
                    have : k < d' := h_k_lt
                    have : d' * d' > n := h_sq_gt
                    omega
                  omega
                · next h_div_zero =>
                  simp at h_helper_true
                · next h_no_div =>
                  simp at h_helper_true
                  have : isPrime.helper n (d' + 1) = true := h_helper_true
                  by_cases h_eq : k = d'
                  · subst h_eq
                    exact h_no_div
                  · have : k < d' := by
                      have : k < d' ∨ k = d' := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h_k_lt)
                      cases this with
                      | inl h => exact h
                      | inr h => contradiction
                    exact ih d' (Nat.lt_succ_self d') ((d' + 1) * (d' + 1)) (by omega) (by omega) h_helper_true k h_k_ge2 this
            exact this
          have : ∀ k, 2 ≤ k → k < m → n % k ≠ 0 := by
            apply h_helper m
            · have : m < n := h_m_lt
              have : m * m ≤ m * n := Nat.mul_le_mul_left m (Nat.le_of_lt h_m_lt)
              have : m * n < n * n := Nat.mul_lt_mul_right (Nat.pos_of_ne_zero (by
                by_contra h_zero
                rw [h_zero] at h_m_lt
                exact Nat.lt_irrefl 0 h_m_lt)) h_m_lt
              omega
            · exact h_m_ge
            · exact this
          have : n % m ≠ 0 := by
            have : m < n := h_m_lt
            have : m ≠ n := Nat.ne_of_lt h_m_lt
            by_contra h_div_zero
            rw [Nat.dvd_iff_mod_eq_zero] at h_div_zero
            exact h_div (Nat.dvd_of_mod_eq_zero h_div_zero)
          exact this h_div
  · intro h
    simp [isPrime]
    split
    · next h_lt =>
      have : n ≥ 2 := Nat.Prime.two_le h
      omega
    · next h_ge =>
      have h_ge_2 : n ≥ 2 := Nat.Prime.two_le h
      simp [isPrime.helper]
      have : ∀ d, d ≥ 2 → isPrime.helper n d = true := by
        intro d h_d_ge2
        have : ∀ k, 2 ≤ k → k < n → n % k ≠ 0 := by
          intro k h_k_ge2 h_k_lt
          rw [← Nat.dvd_iff_mod_eq_zero]
          intro h_div
          have : k = 1 ∨ k = n := Nat.dvd_prime.mp h h_div
          cases this with
          | inl h_eq => 
            rw [h_eq] at h_k_ge2
            omega
          | inr h_eq =>
            rw [h_eq] at h_k_lt
            exact Nat.lt_irrefl n h_k_lt
        induction d using Nat.strong_induction_on with
        | h d' ih =>
          simp [isPrime.helper]
          split
          · next h_sq_gt => rfl
          · next h_sq_le =>
            split
            · next h_div_zero =>
              have : n % d' ≠ 0 := this d' h_d_ge2 (by
                have : d' * d' ≤ n := Nat.le_of_not_gt h_sq_le
                have : d' ≤ n := by
                  by_contra h_gt
                  simp at h_gt
                  have : d' * d' > n * 1 := by
                    rw [Nat.mul_one]
                    exact Nat.mul_lt_mul_right (Nat.pos_of_ne_zero (by
                      by_contra h_zero
                      rw [h_zero] at h_d_ge2
                      omega)) h_gt
                  omega
                have : d' < n := by
                  by_contra h_ge
                  simp at h_ge
                  have : d' = n := Nat.eq_of_le_of_lt_succ h_ge (Nat.lt_succ_of_le h_ge)
                  rw [this] at h_div_zero
                  have : n % n = 0 := Nat.mod_self n
                  rw [this] at h_div_zero
                  simp at h_div_zero
                exact this)
              simp at h_div_zero
            · next h_no_div =>
              exact ih (d' + 1) (Nat.lt_succ_self d') (by omega)
      exact this 2 (by omega)

-- LLM HELPER
lemma primesBelow_correct (n: Nat) : 
  ∀ i : Nat, i ∈ primesBelow n ↔ (i < n ∧ Nat.Prime i) := by
  intro i
  constructor
  · intro h_mem
    constructor
    · simp [primesBelow] at h_mem
      have : ∀ j ∈ primesBelow n, j < n := by
        intro j h_j_mem
        simp [primesBelow] at h_j_mem
        have : ∀ k acc, j ∈ primesBelow.helper n k acc → (∀ l ∈ acc, l < k) → j < n := by
          intro k acc h_j_helper h_acc_lt
          induction k using Nat.strong_induction_on generalizing acc with
          | h k' ih =>
            simp [primesBelow.helper] at h_j_helper
            split at h_j_helper
            · next h_ge =>
              simp [List.mem_reverse] at h_j_helper
              cases h_j_helper with
              | inl h_eq =>
                subst h_eq
                exact Nat.lt_of_le_of_lt (Nat.le_of_not_gt (by
                  by_contra h_gt
                  exact h_ge h_gt)) (by omega)
              | inr h_in_acc =>
                have : j < k' := h_acc_lt j h_in_acc
                exact Nat.lt_trans this (Nat.le_of_not_gt (by
                  by_contra h_gt
                  exact h_ge h_gt))
            · next h_lt =>
              split at h_j_helper
              · next h_prime =>
                exact ih (k' + 1) (Nat.lt_succ_self k') (j :: acc) h_j_helper (by
                  intro l h_l_mem
                  simp at h_l_mem
                  cases h_l_mem with
                  | inl h_eq =>
                    subst h_eq
                    exact h_lt
                  | inr h_in_acc =>
                    exact Nat.lt_trans (h_acc_lt l h_in_acc) (Nat.le_of_lt h_lt))
              · next h_not_prime =>
                exact ih (k' + 1) (Nat.lt_succ_self k') acc h_j_helper (by
                  intro l h_l_mem
                  exact Nat.lt_trans (h_acc_lt l h_l_mem) (Nat.le_of_lt h_lt))
        exact this 2 [] h_mem (by simp)
      exact this i h_mem
    · rw [← isPrime_correct]
      simp [primesBelow] at h_mem
      have : ∀ j ∈ primesBelow n, isPrime j = true := by
        intro j h_j_mem
        simp [primesBelow] at h_j_mem
        have : ∀ k acc, j ∈ primesBelow.helper n k acc → (∀ l ∈ acc, isPrime l = true) → isPrime j = true := by
          intro k acc h_j_helper h_acc_prime
          induction k using Nat.strong_induction_on generalizing acc with
          | h k' ih =>
            simp [primesBelow.helper] at h_j_helper
            split at h_j_helper
            · next h_ge =>
              simp [List.mem_reverse] at h_j_helper
              cases h_j_helper with
              | inl h_eq =>
                subst h_eq
                have : isPrime k' = true := by
                  simp [primesBelow.helper] at h_j_helper
                  have : j ∈ (k' :: acc).reverse := h_j_helper
                  simp [List.mem_reverse] at this
                  cases this with
                  | inl h_eq2 =>
                    subst h_eq2
                    have : ∃ k₀ acc₀, k₀ < k' ∧ primesBelow.helper n k₀ acc₀ = (k' :: acc).reverse := by
                      use k' - 1, acc
                      constructor
                      · omega
                      · simp [primesBelow.helper]
                        split
                        · next h_ge2 =>
                          have : k' - 1 ≥ n := h_ge2
                          have : k' ≥ n := by omega
                          exact h_ge h_ge2
                        · next h_lt2 =>
                          split
                          · next h_prime2 =>
                            have : primesBelow.helper n k' (k' - 1 :: acc) = (k' :: acc).reverse := by
                              simp [primesBelow.helper]
                              split
                              · next h_ge3 => rfl
                              · next h_lt3 =>
                                exfalso
                                exact h_ge h_lt3
                            rw [this]
                            rfl
                          · next h_not_prime2 =>
                            exfalso
                            have : k' - 1 < k' := by omega
                            have : primesBelow.helper n k' acc = (k' :: acc).reverse := by
                              simp [primesBelow.helper]
                              split
                              · next h_ge3 => rfl
                              · next h_lt3 =>
                                exfalso
                                exact h_ge h_lt3
                            rw [this] at h_not_prime2
                            simp at h_not_prime2
                    obtain ⟨k₀, acc₀, h_k₀_lt, h_eq⟩ := this
                    rw [← h_eq] at h_j_helper
                    have : j ∈ primesBelow.helper n k₀ acc₀ := h_j_helper
                    exact ih k₀ h_k₀_lt acc₀ this h_acc_prime
                  | inr h_in_acc =>
                    exact h_acc_prime j h_in_acc
                rw [h_eq] at this
                exact this
              | inr h_in_acc =>
                exact h_acc_prime j h_in_acc
            · next h_lt =>
              split at h_j_helper
              · next h_prime =>
                exact ih (k' + 1) (Nat.lt_succ_self k') (k' :: acc) h_j_helper (by
                  intro l h_l_mem
                  simp at h_l_mem
                  cases h_l_mem with
                  | inl h_eq =>
                    subst h_eq
                    exact h_prime
                  | inr h_in_acc =>
                    exact h_acc_prime l h_in_acc)
              · next h_not_prime =>
                exact ih (k' + 1) (Nat.lt_succ_self k') acc h_j_helper h_acc_prime
        exact this 2 [] h_mem (by simp)
      exact this i h_mem
  · intro h
    simp [primesBelow]
    have h_lt : i < n := h.1
    have h_prime : Nat.Prime i := h.2
    have h_is_prime : isPrime i = true := isPrime_correct i |>.mpr h_prime
    have h_ge_2 : i ≥ 2 := Nat.Prime.two_le h_prime
    have : ∀ k acc, k ≤ i → (∀ l ∈ acc, l < k ∧ isPrime l = true) → i ∈ primesBelow.helper n k acc := by
      intro k acc h_k_le h_acc_prop
      induction k using Nat.strong_induction_on generalizing acc with
      | h k' ih =>
        simp [primesBelow.helper]
        split
        · next h_ge =>
          simp [List.mem_reverse]
          by_cases h_eq : i = k'
          · left
            exact h_eq
          · right
            apply h_acc_prop
            rw [h_eq] at h_k_le
            exact h_k_le
        · next h_lt_n =>
          split
          · next h_prime_k =>
            by_cases h_eq : i = k'
            · subst h_eq
              exact ih (k' + 1) (Nat.lt_succ_self k') (k' :: acc) (by omega) (by
                intro l h_l_mem
                simp at h_l_mem
                cases h_l_mem with
                | inl h_eq2 =>
                  subst h_eq2
                  exact ⟨h_lt_n, h_prime_k⟩
                | inr h_in_acc =>
                  have ⟨h_l_lt, h_l_prime⟩ := h_acc_prop l h_in_acc
                  exact ⟨Nat.lt_trans h_l_lt (Nat.le_of_lt h_lt_n), h_l_prime⟩)
            · exact ih (k' + 1) (Nat.lt_succ_self k') (k' :: acc) (by
                have : k' < i := Nat.lt_of_le_of_ne h_k_le (Ne.symm h_eq)
                omega) (by
                intro l h_l_mem
                simp at h_l_mem
                cases h_l_mem with
                | inl h_eq2 =>
                  subst h_eq2
                  exact ⟨h_lt_n, h_prime_k⟩
                | inr h_in_acc =>
                  have ⟨h_l_lt, h_l_prime⟩ := h_acc_prop l h_in_acc
                  exact ⟨Nat.lt_trans h_l_lt (Nat.le_of_lt h_lt_n), h_l_prime⟩)
          · next h_not_prime_k =>
            exact ih (k' + 1) (Nat.lt_succ_self k') acc (by
              by_cases h_eq : i = k'
              · subst h_eq
                rw [h_is_prime] at h_not_prime_k
                simp at h_not_prime_k
              · have : k' < i := Nat.lt_of_le_of_ne h_k_le (Ne.symm h_eq)
                omega) (by
              intro l h_l_mem
              have ⟨h_l_lt, h_l_prime⟩ := h_acc_prop l h_l_mem
              exact ⟨Nat.lt_trans h_l_lt (Nat.le_of_lt h_lt_n), h_l_prime⟩)
    exact this 2 [] h_ge_2 (by simp)

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