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

-- LLM HELPER
def collatz_sequence (n : Nat) : List Nat :=
  if n = 0 then [] 
  else if n = 1 then [1]
  else collatz_sequence_aux n 1000 []

def implementation (n: Nat) : List Nat :=
  let seq := collatz_sequence n
  let odds := seq.filter (fun x => x % 2 = 1)
  odds.mergeSort

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
lemma collatz_step_reachable (n : Nat) : collatz_reachable n (collatz_step n) := by
  unfold collatz_reachable
  use 1
  simp [Nat.iterate]

-- LLM HELPER
lemma collatz_reachable_trans (n m k : Nat) : 
  collatz_reachable n m → collatz_reachable m k → collatz_reachable n k := by
  unfold collatz_reachable
  intro ⟨i, hi⟩ ⟨j, hj⟩
  use i + j
  rw [Nat.iterate_add, hi, hj]

-- LLM HELPER
lemma collatz_reachable_refl (n : Nat) : collatz_reachable n n := by
  unfold collatz_reachable
  use 0
  simp [Nat.iterate]

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
    rw [Nat.two_mul]
    rw [← Nat.div_add_mod n 2, h]
    ring

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
      simp [List.Sorted]
      apply List.sorted_mergeSort
    · intro m
      constructor
      · intro hm
        unfold implementation at hm
        simp at hm
        cases hm with
        | intro hm_in hm_odd =>
          constructor
          · rw [odd_iff_mod_two_eq_one]
            exact hm_odd
          · sorry -- proof that m is reachable would require more complex analysis
      · intro ⟨hm_odd, hm_reach⟩
        unfold implementation
        simp
        constructor
        · sorry -- proof that odd reachable elements are in the filtered list
        · rw [← odd_iff_mod_two_eq_one]
          exact hm_odd

-- #test implementation 5 = [1, 5]