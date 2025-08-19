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
def is_power_of_aux (x: Int) (n: Int) (fuel: Nat) : Bool :=
match fuel with
| 0 => false
| Nat.succ fuel' =>
  if x = 1 then true
  else if x < 1 then false
  else if n <= 1 then false
  else if x % n ≠ 0 then false
  else is_power_of_aux (x / n) n fuel'

def implementation (x: Int) (n: Int) : Bool := 
  if x = 1 then true
  else if x < 1 then false
  else if n <= 1 then false
  else is_power_of_aux x n 100

-- LLM HELPER
lemma power_of_one_is_one (k: Nat) : (1: Int)^k = 1 := by
  induction k with
  | zero => simp
  | succ k ih => simp [pow_succ, ih]

-- LLM HELPER
lemma implementation_true_implies_power (x n: Int) :
  implementation x n = true → ∃ k: Nat, x = n^k := by
  intro h
  simp [implementation] at h
  split_ifs at h with h1 h2 h3
  · exists 0
    simp [h1]
  · contradiction
  · contradiction
  · sorry

theorem correctness
(x: Int) (n: Int)
: problem_spec implementation x n := by
  simp [problem_spec]
  exists implementation x n
  constructor
  · rfl
  · intro h
    exact implementation_true_implies_power x n h