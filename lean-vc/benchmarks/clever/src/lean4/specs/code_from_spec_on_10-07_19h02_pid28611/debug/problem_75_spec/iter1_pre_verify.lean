import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: Int → Bool)
-- inputs
(a: Int) :=
-- spec
let spec (result: Bool) :=
  (a < 100) →
    result ↔ exists a' b c, (Nat.Prime a') ∧ (Nat.Prime b) ∧ (Nat.Prime c) ∧ (a == a'*b*c)
-- program termination
∃ result, implementation a = result ∧
spec result

-- LLM HELPER
def is_prime (n : Nat) : Bool :=
  if n < 2 then false
  else 
    let rec check_divisors (d : Nat) : Bool :=
      if d * d > n then true
      else if n % d == 0 then false
      else check_divisors (d + 1)
    check_divisors 2

-- LLM HELPER
def check_triple_prime_product (a : Int) : Bool :=
  if a <= 0 then false
  else
    let n := a.natAbs
    let rec check_factors (p1 : Nat) : Bool :=
      if p1 * p1 * p1 > n then false
      else if is_prime p1 then
        let rec check_second (p2 : Nat) : Bool :=
          if p1 * p2 * p2 > n then false
          else if is_prime p2 then
            let rec check_third (p3 : Nat) : Bool :=
              if p1 * p2 * p3 > n then false
              else if is_prime p3 ∧ p1 * p2 * p3 == n then true
              else check_third (p3 + 1)
            if check_third p2 then true
            else check_second (p2 + 1)
          else check_second (p2 + 1)
        if check_second p1 then true
        else check_factors (p1 + 1)
      else check_factors (p1 + 1)
    check_factors 2

def implementation (a: Int) : Bool := 
  if a < 100 then check_triple_prime_product a
  else false

-- LLM HELPER
lemma is_prime_correct (n : Nat) : is_prime n = true ↔ Nat.Prime n := by
  constructor
  · intro h
    simp [is_prime] at h
    split at h
    · simp at h
    · rename_i h_ge
      simp at h_ge
      sorry -- The proof that our primality check is correct
  · intro h
    simp [is_prime]
    split
    · simp [Nat.Prime] at h
      sorry -- Contradiction since prime must be ≥ 2
    · sorry -- The proof that prime numbers pass our check

theorem correctness
(a: Int)
: problem_spec implementation a
:= by
  simp [problem_spec]
  use implementation a
  constructor
  · rfl
  · intro h
    simp [implementation]
    split
    · rename_i h_lt
      simp [check_triple_prime_product]
      constructor
      · intro h_check
        split at h_check
        · simp at h_check
        · rename_i h_pos
          sorry -- Proof that if check returns true, then there exist primes
      · intro h_exists
        obtain ⟨a', b, c, ha_prime, hb_prime, hc_prime, h_eq⟩ := h_exists
        sorry -- Proof that if primes exist, then check returns true
    · rename_i h_ge
      simp at h_ge
      have : ¬(a < 100) := by linarith
      contradiction