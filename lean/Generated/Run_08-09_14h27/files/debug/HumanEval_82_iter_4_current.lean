/- 
function_signature: "def prime_length(s: str) -> bool"
docstring: |
    Write a function that takes a string and returns True if the string
    length is a prime number or False otherwise
test_cases:
  - input: "Hello"
    output: True
  - input: "abcdcba"
    output: True
  - input: "kittens"
    output: True
  - input: "orange"
    output: False
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def is_prime_bool (n: Nat) : Bool :=
  if n < 2 then false
  else
    let rec check_divisors (n : Nat) (k: Nat) : Bool :=
      if k * k > n then true
      else if n % k = 0 then false
      else check_divisors n (k + 1)
    termination_by n - k
    decreasing_by
      simp_wf
      omega
    check_divisors n 2

def implementation (s: String) : Bool :=
  is_prime_bool s.length

def problem_spec
-- function signature
(implementation: String → Bool)
-- inputs
(s: String) :=
-- spec
let spec (result : Bool) :=
let is_prime (n: Nat) : Prop :=
  n ≥ 2 ∧ ¬ (∃ k, 2 ≤ k ∧ k < n ∧ n % k = 0);
  result ↔ is_prime s.length
-- program termination
∃ result,
  implementation s = result ∧
  spec result

-- LLM HELPER
lemma check_divisors_correct (n k : Nat) (h : 2 ≤ k) : 
  is_prime_bool.check_divisors n k = true ↔ (∀ x, k ≤ x → x < n → x * x ≤ n → ¬(n % x = 0)) := by
  induction k, n using is_prime_bool.check_divisors.induct generalizing h
  case case1 n k h1 =>
    simp [is_prime_bool.check_divisors, h1]
    constructor
    · intro _
      intros x hx_ge hx_lt hx_sq hdiv
      have : x * x > n := by
        apply Nat.lt_of_le_of_lt hx_sq
        exact h1
      omega
    · intro _
      trivial
  case case2 n k h1 h2 =>
    simp [is_prime_bool.check_divisors, h1, h2]
  case case3 n k h1 h2 ih =>
    simp [is_prime_bool.check_divisors, h1, h2]
    constructor
    · intro h_rec x hx_ge hx_lt hx_sq
      by_cases hx_eq : x = k
      · subst hx_eq
        exact h2
      · have hx_gt : k < x := Nat.lt_of_le_of_ne hx_ge hx_eq
        have h_succ : k + 1 ≤ x := Nat.succ_le_of_lt hx_gt
        have ih_app := ih (by omega)
        rw [ih_app] at h_rec
        exact h_rec x h_succ hx_lt hx_sq
    · intro h_all
      have ih_app := ih (by omega)
      rw [ih_app]
      intros x hx_ge hx_lt hx_sq
      exact h_all x (Nat.le_trans (Nat.le_succ k) hx_ge) hx_lt hx_sq

-- LLM HELPER
lemma is_prime_bool_correct (n: Nat) : 
  is_prime_bool n = true ↔ (n ≥ 2 ∧ ¬ (∃ k, 2 ≤ k ∧ k < n ∧ n % k = 0)) := by
  simp [is_prime_bool]
  constructor
  · intro h
    simp at h
    cases h_lt : n < 2 with
    | true =>
      simp [h_lt] at h
    | false =>
      simp [h_lt] at h
      constructor
      · omega
      · by_contra h_contra
        obtain ⟨k, hk_ge, hk_lt, hk_div⟩ := h_contra
        have h_check := check_divisors_correct n 2 (by norm_num)
        rw [h_check] at h
        have : k * k ≤ n := by
          by_contra h_not
          push_neg at h_not
          have h_sqrt : ∀ x, 2 ≤ x → x * x ≤ n → x < k := by
            intros x hx_ge hx_sq
            by_contra h_not_lt
            push_neg at h_not_lt
            have : k ≤ x := h_not_lt
            have : k * k ≤ x * x := Nat.mul_self_le_mul_self this
            have : n < k * k := h_not
            have : n < x * x := Nat.lt_of_lt_of_le this (Nat.le_trans (Nat.le_refl _) ‹k * k ≤ x * x›)
            omega
          have : k < k := h_sqrt k hk_ge this
          omega
        have : ¬(n % k = 0) := h k (by omega) hk_lt this
        exact this hk_div
  · intro ⟨h_ge, h_no_div⟩
    simp
    have h_not_lt : ¬(n < 2) := by omega
    simp [h_not_lt]
    have h_check := check_divisors_correct n 2 (by norm_num)
    rw [h_check]
    intros x hx_ge hx_lt hx_sq hdiv
    have : ∃ k, 2 ≤ k ∧ k < n ∧ n % k = 0 := ⟨x, by omega, hx_lt, hdiv⟩
    exact h_no_div this

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  simp [problem_spec]
  use implementation s
  constructor
  · rfl
  · simp [implementation]
    rw [is_prime_bool_correct]

-- #test implementation "Hello" = True
-- #test implementation "abcdcba" = True
-- #test implementation "kittens" = True
-- #test implementation "orange" = False