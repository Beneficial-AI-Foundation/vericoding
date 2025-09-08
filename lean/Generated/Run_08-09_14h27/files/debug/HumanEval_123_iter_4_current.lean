import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

/--
name: collatz_reachable
use: |
  Helper to check if a natural number m is reachable in the Collatz sequence starting at n.
problems:
  - 123
-/
def collatz_reachable (n m : Nat) : Prop :=
  ∃ k, Nat.iterate (fun x => if x % 2 = 0 then x / 2 else x * 3 + 1) k n = m

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def collatz_step (x : Nat) : Nat :=
  if x % 2 = 0 then x / 2 else x * 3 + 1

-- LLM HELPER
def collatz_sequence_aux (current : Nat) (steps : Nat) (acc : List Nat) : List Nat :=
  if steps = 0 || current = 1 then 
    acc.reverse
  else
    let next := collatz_step current
    collatz_sequence_aux next (steps - 1) (current :: acc)
termination_by steps
decreasing_by
  simp_wf
  have h : ¬(decide (steps = 0) || decide (current = 1)) = true := by assumption
  simp [decide_eq_true_eq] at h
  push_neg at h
  exact Nat.zero_lt_of_ne_zero h.1

-- LLM HELPER
def collatz_sequence (n : Nat) : List Nat :=
  if n = 0 then [] 
  else if n = 1 then [1]
  else collatz_sequence_aux n 1000 []

def implementation (n: Nat) : List Nat :=
  let seq := collatz_sequence n
  let odds := seq.filter (fun x => x % 2 = 1)
  odds.mergeSort (fun a b => decide (a ≤ b))

def problem_spec
-- function signature
(impl: Nat → List Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: List Nat) :=
n > 0 →
result.Sorted (· < ·) ∧
∀ m, m ∈ result ↔ Odd m ∧ collatz_reachable n m -- m is reachable from starting point n
-- program termination
∃ result, impl n = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma collatz_step_eq (n : Nat) : (if n % 2 = 0 then n / 2 else n * 3 + 1) = collatz_step n := by
  unfold collatz_step
  rfl

-- LLM HELPER
lemma iterate_composition (f : Nat → Nat) (n m k i j : Nat) :
  f^[i] n = m → f^[j] m = k → f^[i + j] n = k := by
  intro hi hj
  rw [Function.iterate_add_apply, hi, hj]

-- LLM HELPER
lemma collatz_step_reachable (n : Nat) : collatz_reachable n (collatz_step n) := by
  unfold collatz_reachable
  use 1
  simp [collatz_step_eq]

-- LLM HELPER
lemma collatz_reachable_trans (n m k : Nat) : 
  collatz_reachable n m → collatz_reachable m k → collatz_reachable n k := by
  unfold collatz_reachable
  intro ⟨i, hi⟩ ⟨j, hj⟩
  use i + j
  exact iterate_composition _ n m k i j hi hj

-- LLM HELPER
lemma collatz_reachable_refl (n : Nat) : collatz_reachable n n := by
  unfold collatz_reachable
  use 0
  simp [Function.iterate_zero]

-- LLM HELPER
lemma odd_iff_mod_two_eq_one (n : Nat) : Odd n ↔ n % 2 = 1 := by
  constructor
  · intro h
    cases h with
    | intro k hk =>
      rw [hk]
      simp [Nat.add_mod]
  · intro h
    use n / 2
    have : n = n / 2 * 2 + n % 2 := (Nat.div_add_mod n 2).symm
    rw [h] at this
    rw [← this, Nat.mul_comm]
    ring

-- LLM HELPER  
lemma list_sorted_mergeSort_decide (l : List Nat) : 
  (l.mergeSort (fun a b => decide (a ≤ b))).Sorted (· < ·) := by
  have h1 := List.sorted_mergeSort (fun a b => decide (a ≤ b)) l
  apply List.Sorted.imp _ h1
  intro a b hab
  simp [decide_eq_true_eq] at hab
  by_cases h : a = b
  · rw [h] at hab
    simp at hab
  · exact Nat.lt_of_le_of_ne hab h

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  unfold problem_spec
  use implementation n
  constructor
  · rfl
  · intro hn
    constructor
    · unfold implementation
      exact list_sorted_mergeSort_decide _
    · intro m
      constructor
      · intro hm
        unfold implementation at hm
        simp at hm
        constructor
        · rw [odd_iff_mod_two_eq_one]
          exact hm.2
        · unfold collatz_reachable
          use 0
          simp
      · intro ⟨hm_odd, hm_reach⟩
        unfold implementation
        simp
        constructor
        · unfold collatz_reachable at hm_reach
          cases hm_reach with
          | intro k hk =>
            have : m = n := by
              rw [← hk]
              simp [Function.iterate_zero]
            rw [this]
            trivial
        · rw [← odd_iff_mod_two_eq_one]
          exact hm_odd

-- #test implementation 5 = [1, 5]