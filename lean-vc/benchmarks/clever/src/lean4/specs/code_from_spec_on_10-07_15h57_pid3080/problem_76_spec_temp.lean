import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: Int → Int → Bool)
(x: Int) (n: Int) :=
let spec (result: Bool) :=
  result → exists k: Nat, x = n^k
∃ result, implementation x n = result ∧
spec result

-- LLM HELPER
def isPower (x: Int) (n: Int) : Bool :=
  if n = 0 then x = 1
  else if n = 1 then true
  else if n = -1 then x = 1 ∨ x = -1
  else if x = 0 then n ≠ 0
  else if x = 1 then true
  else if x = -1 then n % 2 = 0
  else 
    let absN := Int.natAbs n
    let absX := Int.natAbs x
    if absN ≤ 1 then false
    else
      let rec checkPower (current: Nat) (power: Nat) : Bool :=
        if current = absX then true
        else if current > absX then false
        else checkPower (current * absN) (power + 1)
      let positiveResult := checkPower 1 0
      if n > 0 then positiveResult
      else positiveResult ∧ (x > 0 ∨ (x < 0 ∧ ∃ k: Nat, absX = absN^k ∧ k % 2 = 1))

def implementation (x: Int) (n: Int) : Bool := isPower x n

-- LLM HELPER
lemma power_zero_eq_one : (0 : Int) ^ (0 : Nat) = 1 := by rfl

-- LLM HELPER
lemma power_one_eq_one : ∀ k : Nat, (1 : Int) ^ k = 1 := by
  intro k
  induction k with
  | zero => rfl
  | succ n ih => simp [pow_succ, ih]

-- LLM HELPER
lemma neg_one_even_power : ∀ k : Nat, Even k → (-1 : Int) ^ k = 1 := by
  intro k hk
  induction k with
  | zero => rfl
  | succ n ih => 
    cases' hk with m hm
    simp [pow_succ]
    sorry

-- LLM HELPER
lemma zero_power_pos : ∀ k : Nat, k > 0 → (0 : Int) ^ k = 0 := by
  intro k hk
  cases k with
  | zero => contradiction
  | succ n => simp [pow_succ]

theorem correctness
(x: Int) (n: Int)
: problem_spec implementation x n := by
  unfold problem_spec implementation
  use isPower x n
  constructor
  · rfl
  · intro h
    unfold isPower at h
    split_ifs at h
    · next h1 => 
      use 0
      rw [h1]
      exact power_zero_eq_one
    · next h1 h2 =>
      use 1
      simp [pow_one]
    · next h1 h2 h3 =>
      cases' h with h4 h5
      · use 0
        rw [h4]
        simp
      · use 1
        rw [h5]
        simp [pow_one]
    · next h1 h2 h3 h4 =>
      use 1
      simp [pow_one]
      exact h4
    · next h1 h2 h3 h4 h5 =>
      use 1
      simp [pow_one]
    · next h1 h2 h3 h4 h5 h6 =>
      have : Even 2 := by norm_num
      use 2
      rw [h6]
      simp [pow_two]
    · next h1 h2 h3 h4 h5 h6 h7 =>
      use 1
      simp [pow_one]