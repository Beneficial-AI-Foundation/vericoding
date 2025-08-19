import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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
      if (Nat.digits 10 rest).all (fun x => x % 2 = 0)
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

def implementation (n: Nat) : Nat := 
  if n = 0 then 0
  else if n < 10 then 
    if n % 2 = 1 then n else 0
  else
    let digit := n % 10
    let rest := n / 10
    if digit % 2 = 1 then
      if (Nat.digits 10 rest).all (fun x => x % 2 = 0) then
        digit
      else
        implementation rest * digit
    else
      implementation rest

-- LLM HELPER
lemma nat_pos_cases (n : Nat) : n = 0 ∨ (0 < n ∧ n < 10) ∨ (10 ≤ n) := by
  by_cases h1 : n = 0
  · left; exact h1
  · by_cases h2 : n < 10
    · right; left; constructor
      · exact Nat.pos_of_ne_zero h1
      · exact h2
    · right; right; exact Nat.le_of_not_gt (fun h => h2 (Nat.lt_of_succ_le (Nat.succ_le_of_lt h)))

-- LLM HELPER
lemma even_digit_mod_two (d : Nat) : d % 2 = 0 ∨ d % 2 = 1 := by
  exact Nat.mod_two_eq_zero_or_one d

-- LLM HELPER
lemma implementation_zero : implementation 0 = 0 := by
  rfl

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  unfold problem_spec
  simp only [implementation]
  cases' nat_pos_cases n with h h
  · -- n = 0 case
    subst h
    use 0
    simp [implementation_zero]
  · cases' h with h h
    · -- 0 < n < 10 case
      cases' h with hn_pos hn_lt_10
      use if n % 2 = 1 then n else 0
      constructor
      · simp [implementation]
        rw [if_neg (Ne.symm (ne_of_gt hn_pos))]
        rw [if_pos hn_lt_10]
      · intro hn_pos'
        constructor
        · intro hn_lt_10'
          cases' even_digit_mod_two n with h_even h_odd
          · -- n even
            constructor
            · intro h_odd_contra
              rw [h_even] at h_odd_contra
              simp at h_odd_contra
            · intro h_even_hyp
              simp [implementation]
              rw [if_neg (Ne.symm (ne_of_gt hn_pos))]
              rw [if_pos hn_lt_10]
              rw [if_neg]
              rw [h_even]
              simp
          · -- n odd
            constructor
            · intro h_odd_hyp
              simp [implementation]
              rw [if_neg (Ne.symm (ne_of_gt hn_pos))]
              rw [if_pos hn_lt_10]
              rw [if_pos h_odd]
            · intro h_even_hyp
              rw [h_odd] at h_even_hyp
              simp at h_even_hyp
        · intro hn_ge_10
          have : ¬(n ≥ 10) := not_le.mpr hn_lt_10
          contradiction
    · -- n ≥ 10 case
      let digit := n % 10
      let rest := n / 10
      use implementation n
      constructor
      · rfl
      · intro hn_pos
        constructor
        · intro hn_lt_10
          have : ¬(n < 10) := not_lt.mpr h
          contradiction
        · intro hn_ge_10
          cases' even_digit_mod_two digit with h_even h_odd
          · -- digit even
            constructor
            · intro h_odd_contra
              rw [h_even] at h_odd_contra
              simp at h_odd_contra
            · intro h_even_hyp
              simp [implementation]
              have : ¬(n = 0) := Ne.symm (ne_of_gt hn_pos)
              have : ¬(n < 10) := not_lt.mpr h
              rw [if_neg ‹¬(n = 0)›, if_neg ‹¬(n < 10)›]
              rw [if_neg]
              rw [h_even]
              simp
          · -- digit odd
            constructor
            · intro h_odd_hyp
              simp [implementation]
              have : ¬(n = 0) := Ne.symm (ne_of_gt hn_pos)
              have : ¬(n < 10) := not_lt.mpr h
              rw [if_neg ‹¬(n = 0)›, if_neg ‹¬(n < 10)›]
              rw [if_pos h_odd]
              by_cases h_all : (Nat.digits 10 rest).all (fun x => x % 2 = 0)
              · rw [if_pos h_all]
                constructor <;> rfl
              · rw [if_neg h_all]
                rfl
            · intro h_even_hyp
              rw [h_odd] at h_even_hyp
              simp at h_even_hyp