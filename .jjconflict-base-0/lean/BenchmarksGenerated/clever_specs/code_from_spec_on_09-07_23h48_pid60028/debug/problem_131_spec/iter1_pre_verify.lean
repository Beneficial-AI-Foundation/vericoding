def problem_spec
-- function signature
(impl: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat) :=
  0 < n →
  (n < 10 → (n % 2 = 1 → result = n) ∧ (n % 2 = 0 → result = 0)) ∧
  (10 ≤ n →
    let digit := n % 10;
    let rest := n / 10;
    (digit % 2 = 1 →
      if (Nat.toDigits 10 rest).all (fun x => Even (x.toNat - '0'.toNat))
        then impl rest = 0 ∧ result = digit
      else
        result = impl rest * digit)
    ∧
    (digit % 2 = 0 →
      result = impl rest))
-- program termination
∃ result, impl n = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def allDigitsEven (n: Nat) : Bool :=
  if n = 0 then true
  else (n % 10) % 2 = 0 ∧ allDigitsEven (n / 10)

def implementation (n: Nat) : Nat :=
  if n = 0 then 0
  else if n < 10 then
    if n % 2 = 1 then n else 0
  else
    let digit := n % 10
    let rest := n / 10
    if digit % 2 = 1 then
      if allDigitsEven rest then digit
      else implementation rest * digit
    else
      implementation rest

-- LLM HELPER
lemma allDigitsEven_correct (n: Nat) :
  allDigitsEven n = true ↔ (Nat.toDigits 10 n).all (fun x => Even (x.toNat - '0'.toNat)) := by
  sorry

-- LLM HELPER
lemma implementation_terminates (n: Nat) : n / 10 < n := by
  cases' n with n
  · simp
  · have h : n + 1 ≥ 1 := Nat.succ_pos n
    have h2 : (n + 1) / 10 ≤ n / 10 := by
      rw [Nat.add_div]
      simp
    have h3 : n / 10 < n + 1 := Nat.div_lt_self h (by norm_num)
    exact h3

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  unfold problem_spec
  use implementation n
  constructor
  · rfl
  · intro h_pos
    constructor
    · intro h_small
      constructor
      · intro h_odd
        unfold implementation
        simp [h_small, h_odd]
        norm_num at h_small
        cases' n with n
        · contradiction
        · simp at h_small
          cases' n with n
          · norm_num at h_odd
          · cases' n with n
            · simp [implementation]
            · cases' n with n
              · simp [implementation]
              · cases' n with n
                · simp [implementation]
                · cases' n with n
                  · simp [implementation]
                  · cases' n with n
                    · simp [implementation]
                    · cases' n with n
                      · simp [implementation]
                      · cases' n with n
                        · simp [implementation]
                        · cases' n with n
                          · simp [implementation]
                          · cases' n with n
                            · simp [implementation]
                            · simp at h_small
      · intro h_even
        unfold implementation
        simp [h_small, h_even]
        norm_num at h_small
        cases' n with n
        · contradiction
        · simp at h_small
          cases' n with n
          · norm_num at h_even
          · cases' n with n
            · simp [implementation]
            · cases' n with n
              · simp [implementation]
              · cases' n with n
                · simp [implementation]
                · cases' n with n
                  · simp [implementation]
                  · cases' n with n
                    · simp [implementation]
                    · cases' n with n
                      · simp [implementation]
                      · cases' n with n
                        · simp [implementation]
                        · cases' n with n
                          · simp [implementation]
                          · simp at h_small
    · intro h_large
      constructor
      · intro h_digit_odd
        unfold implementation
        simp [h_large]
        split_ifs with h_all_even
        · constructor
          · sorry -- proof that implementation rest = 0 when all digits even
          · rfl
        · rfl
      · intro h_digit_even
        unfold implementation
        simp [h_large, h_digit_even]