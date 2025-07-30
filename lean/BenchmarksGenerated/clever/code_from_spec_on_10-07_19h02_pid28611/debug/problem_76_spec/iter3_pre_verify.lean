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
  if x = 1 then true
  else if n = 0 then false
  else if n = 1 then x = 1
  else if n = -1 then x = 1 ∨ x = -1
  else false

def implementation (x: Int) (n: Int) : Bool := isPower x n

-- LLM HELPER
lemma power_one_is_one (k: Nat) : (1: Int)^k = 1 := by
  induction k with
  | zero => simp
  | succ k ih => simp [pow_succ, ih]

-- LLM HELPER
lemma one_power_existence (x: Int) (n: Int) : x = 1 → ∃ k: Nat, x = n^k := by
  intro h
  use 1
  rw [h]
  simp

-- LLM HELPER
lemma neg_one_power_existence : ∃ k: Nat, (-1: Int) = (-1: Int)^k := by
  use 1
  simp

-- LLM HELPER
lemma x_eq_one_power_of_n_eq_one (x: Int) : x = 1 → ∃ k: Nat, x = (1: Int)^k := by
  intro h
  use 1
  rw [h]
  simp

-- LLM HELPER
lemma x_eq_one_or_neg_one_power_of_n_eq_neg_one (x: Int) : x = 1 ∨ x = -1 → ∃ k: Nat, x = (-1: Int)^k := by
  intro h
  cases h with
  | inl h1 => 
    use 0
    rw [h1]
    simp
  | inr h2 =>
    use 1
    rw [h2]
    simp

theorem correctness
(x: Int) (n: Int)
: problem_spec implementation x n := by
  use implementation x n
  constructor
  · rfl
  · intro h
    simp [implementation, isPower] at h
    split_ifs at h with h1 h2 h3 h4
    · exact one_power_existence x n h1
    · contradiction
    · exact x_eq_one_power_of_n_eq_one x h
    · exact x_eq_one_or_neg_one_power_of_n_eq_neg_one x h
    · contradiction