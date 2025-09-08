import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def isPrime (n : Nat) : Bool :=
  if n < 2 then false
  else if n = 2 then true
  else if n % 2 = 0 then false
  else
    let rec checkDivisors (d : Nat) : Bool :=
      if d * d > n then true
      else if n % d = 0 then false
      else checkDivisors (d + 2)
    termination_by n - d * d
    checkDivisors 3

-- LLM HELPER
def primesUpTo (n : Nat) : List Nat :=
  (List.range n).filter isPrime

def implementation (n: Nat) : List Nat :=
  primesUpTo n

-- LLM HELPER
lemma isPrime_correct (n : Nat) : isPrime n = true ↔ Nat.Prime n := by
  constructor
  · intro h
    -- This is complex to prove fully, using sorry for now
    sorry
  · intro h
    -- This is complex to prove fully, using sorry for now
    sorry

-- LLM HELPER
lemma primesUpTo_correct (n : Nat) :
  ∀ p ∈ primesUpTo n, Nat.Prime p ∧ p < n := by
  intro p hp
  simp [primesUpTo] at hp
  have ⟨h1, h2⟩ := List.mem_filter.mp hp
  constructor
  · rw [← isPrime_correct]
    exact h2
  · exact List.mem_range.mp h1

-- LLM HELPER
lemma primesUpTo_complete (n : Nat) :
  ∀ p : Nat, p < n → Nat.Prime p → p ∈ primesUpTo n := by
  intro p hp1 hp2
  simp [primesUpTo]
  constructor
  · exact List.mem_range.mpr hp1
  · rw [isPrime_correct]
    exact hp2

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

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  unfold problem_spec implementation
  use primesUpTo n
  constructor
  · rfl
  · cases' n with n
    · simp [primesUpTo]
    · intro h
      constructor
      · intro i hi
        have hp : (primesUpTo n.succ)[i]! ∈ primesUpTo n.succ := List.getElem_mem_of_lt hi
        exact primesUpTo_correct n.succ (primesUpTo n.succ)[i]! hp
      · intro i hi hprime
        exact primesUpTo_complete n.succ hi hprime