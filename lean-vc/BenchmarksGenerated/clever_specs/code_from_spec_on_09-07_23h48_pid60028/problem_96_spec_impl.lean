-- LLM HELPER
def Nat.Prime (n : Nat) : Prop := n > 1 ∧ ∀ m : Nat, m ∣ n → m = 1 ∨ m = n

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
    · constructor
      · omega
      · intro m h_div
        by_contra h_not
        push_neg at h_not
        have h_ne_1 : m ≠ 1 := h_not.1
        have h_ne_n : m ≠ n := h_not.2
        have h_m_ge_2 : m ≥ 2 := by
          have h_m_pos : m > 0 := Nat.pos_of_dvd_of_pos h_div (by omega)
          by_cases h_m_eq_1 : m = 1
          · contradiction
          · omega
        have h_m_lt_n : m < n := by
          have h_m_le_n : m ≤ n := Nat.le_of_dvd (by omega) h_div
          exact Nat.lt_of_le_of_ne h_m_le_n h_ne_n
        have h_m_sq_le_n : m * m ≤ n := by
          by_contra h_not_sq
          push_neg at h_not_sq
          have h_helper_true : isPrime.helper n 2 = true := by
            simp [isPrime] at h
            split at h
            · simp at h
            · exact h
          have h_helper_m : isPrime.helper n 2 = true := h_helper_true
          have : ∀ d, d ≥ 2 → d ≤ m → isPrime.helper n d = true → n % d ≠ 0 := by
            intro d h_d_ge h_d_le h_helper_d
            induction d using Nat.strong_induction_on with
            | h d' ih =>
              simp [isPrime.helper] at h_helper_d
              split at h_helper_d
              · contradiction
              · split at h_helper_d
                · simp at h_helper_d
                · exact ih (d' + 1) (Nat.lt_succ_self d') (by omega) (by omega) h_helper_d
          have h_no_div_m : n % m ≠ 0 := this m h_m_ge_2 (le_refl m) h_helper_m
          exact h_no_div_m (Nat.dvd_iff_mod_eq_zero.mp h_div)
        have h_helper_true : isPrime.helper n 2 = true := by
          simp [isPrime] at h
          split at h
          · simp at h
          · exact h
        have : ∀ d, d ≥ 2 → d * d ≤ n → isPrime.helper n d = true → n % d ≠ 0 := by
          intro d h_d_ge h_d_sq h_helper_d
          induction d using Nat.strong_induction_on with
          | h d' ih =>
            simp [isPrime.helper] at h_helper_d
            split at h_helper_d
            · have : d' * d' > n := by assumption
              omega
            · split at h_helper_d
              · simp at h_helper_d
              · exact ih (d' + 1) (Nat.lt_succ_self d') (by omega) (by omega) h_helper_d
        have h_no_div_m : n % m ≠ 0 := this m h_m_ge_2 h_m_sq_le_n h_helper_true
        exact h_no_div_m (Nat.dvd_iff_mod_eq_zero.mp h_div)
  · intro h
    simp [isPrime, Nat.Prime] at h ⊢
    split
    · omega
    · simp [isPrime.helper]
      have : ∀ d, d ≥ 2 → isPrime.helper n d = true := by
        intro d h_d_ge
        induction d using Nat.strong_induction_on with
        | h d' ih =>
          simp [isPrime.helper]
          split
          · rfl
          · split
            · have h_div : d' ∣ n := Nat.dvd_iff_mod_eq_zero.mpr (by assumption)
              have h_cases := h.2 d' h_div
              cases h_cases with
              | inl h_eq => omega
              | inr h_eq => 
                have : d' < n := by
                  by_contra h_not
                  push_neg at h_not
                  have : d' ≥ n := h_not
                  rw [h_eq] at this
                  exact Nat.lt_irrefl n this
                have : d' * d' < n * n := Nat.mul_lt_mul h_eq this
                rw [h_eq] at this
                exact Nat.lt_irrefl (n * n) this
            · exact ih (d' + 1) (Nat.lt_succ_self d') (by omega)
      exact this 2 (by omega)

-- LLM HELPER
lemma primesBelow_mem_iff (n i : Nat) : i ∈ primesBelow n ↔ (i < n ∧ Nat.Prime i) := by
  constructor
  · intro h_mem
    simp [primesBelow] at h_mem
    have h_lt : i < n := by
      have : ∀ j k acc, j ∈ primesBelow.helper n k acc → (∀ l ∈ acc, l < k) → j < n := by
        intro j k acc h_j_mem h_acc_bound
        induction k using Nat.strong_induction_on generalizing acc with
        | h k' ih =>
          simp [primesBelow.helper] at h_j_mem
          split at h_j_mem
          · simp [List.mem_reverse] at h_j_mem
            cases h_j_mem with
            | inl h_eq => 
              subst h_eq
              omega
            | inr h_in_acc =>
              have : j < k' := h_acc_bound j h_in_acc
              omega
          · split at h_j_mem
            · exact ih (k' + 1) (Nat.lt_succ_self k') (j :: acc) h_j_mem (by
                intro l h_l_mem
                simp at h_l_mem
                cases h_l_mem with
                | inl h_eq => 
                  subst h_eq
                  assumption
                | inr h_in_acc =>
                  have : l < k' := h_acc_bound l h_in_acc
                  omega)
            · exact ih (k' + 1) (Nat.lt_succ_self k') acc h_j_mem (by
                intro l h_l_mem
                have : l < k' := h_acc_bound l h_l_mem
                omega)
      exact this i 2 [] h_mem (by simp)
    have h_prime : Nat.Prime i := by
      rw [← isPrime_correct]
      have : ∀ j k acc, j ∈ primesBelow.helper n k acc → (∀ l ∈ acc, isPrime l = true) → isPrime j = true := by
        intro j k acc h_j_mem h_acc_prime
        induction k using Nat.strong_induction_on generalizing acc with
        | h k' ih =>
          simp [primesBelow.helper] at h_j_mem
          split at h_j_mem
          · simp [List.mem_reverse] at h_j_mem
            cases h_j_mem with
            | inl h_eq => 
              subst h_eq
              sorry -- This requires more complex reasoning about how elements get into acc
            | inr h_in_acc =>
              exact h_acc_prime j h_in_acc
          · split at h_j_mem
            · exact ih (k' + 1) (Nat.lt_succ_self k') (k' :: acc) h_j_mem (by
                intro l h_l_mem
                simp at h_l_mem
                cases h_l_mem with
                | inl h_eq => 
                  subst h_eq
                  assumption
                | inr h_in_acc =>
                  exact h_acc_prime l h_in_acc)
            · exact ih (k' + 1) (Nat.lt_succ_self k') acc h_j_mem h_acc_prime
      exact this i 2 [] h_mem (by simp)
    exact ⟨h_lt, h_prime⟩
  · intro ⟨h_lt, h_prime⟩
    simp [primesBelow]
    have h_is_prime : isPrime i = true := isPrime_correct i |>.mpr h_prime
    have h_ge_2 : i ≥ 2 := by
      have ⟨h_gt_1, _⟩ := h_prime
      omega
    have : ∀ k acc, k ≤ i → (∀ l ∈ acc, l < k) → i ∈ primesBelow.helper n k acc := by
      intro k acc h_k_le h_acc_bound
      induction k using Nat.strong_induction_on generalizing acc with
      | h k' ih =>
        simp [primesBelow.helper]
        split
        · simp [List.mem_reverse]
          by_cases h_eq : i = k'
          · left; exact h_eq
          · right
            have : i < k' := Nat.lt_of_le_of_ne h_k_le (Ne.symm h_eq)
            exact h_acc_bound i this
        · split
          · by_cases h_eq : i = k'
            · subst h_eq
              exact ih (k' + 1) (Nat.lt_succ_self k') (k' :: acc) (by omega) (by
                intro l h_l_mem
                simp at h_l_mem
                cases h_l_mem with
                | inl h_eq => 
                  subst h_eq
                  assumption
                | inr h_in_acc =>
                  have : l < k' := h_acc_bound l h_in_acc
                  omega)
            · exact ih (k' + 1) (Nat.lt_succ_self k') (k' :: acc) (by
                have : k' < i := Nat.lt_of_le_of_ne h_k_le (Ne.symm h_eq)
                omega) (by
                intro l h_l_mem
                simp at h_l_mem
                cases h_l_mem with
                | inl h_eq => 
                  subst h_eq
                  assumption
                | inr h_in_acc =>
                  have : l < k' := h_acc_bound l h_in_acc
                  omega)
          · by_cases h_eq : i = k'
            · subst h_eq
              rw [h_is_prime] at *
              simp at *
            · exact ih (k' + 1) (Nat.lt_succ_self k') acc (by
                have : k' < i := Nat.lt_of_le_of_ne h_k_le (Ne.symm h_eq)
                omega) (by
                intro l h_l_mem
                have : l < k' := h_acc_bound l h_l_mem
                omega)
    exact this 2 [] h_ge_2 (by simp)

theorem correctness (n: Nat) : problem_spec implementation n := by
  simp [problem_spec, implementation]
  use primesBelow n
  constructor
  · rfl
  · cases n with
    | zero => 
      simp [primesBelow]
      rfl
    | succ n' =>
      intro h_pos
      constructor
      · intro i h_i_lt
        constructor
        · have h_mem : (primesBelow (n' + 1))[i]! ∈ primesBelow (n' + 1) := by
            apply List.getElem_mem
            exact h_i_lt
          have ⟨h_lt, h_prime⟩ := (primesBelow_mem_iff (n' + 1) ((primesBelow (n' + 1))[i]!)).mp h_mem
          exact h_prime
        · have h_mem : (primesBelow (n' + 1))[i]! ∈ primesBelow (n' + 1) := by
            apply List.getElem_mem
            exact h_i_lt
          have ⟨h_lt, h_prime⟩ := (primesBelow_mem_iff (n' + 1) ((primesBelow (n' + 1))[i]!)).mp h_mem
          exact h_lt
      · intro i h_i_lt h_i_prime
        exact (primesBelow_mem_iff (n' + 1) i).mpr ⟨h_i_lt, h_i_prime⟩