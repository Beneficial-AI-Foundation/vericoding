import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def collatz_step (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

-- LLM HELPER
def collatz_sequence (n : Nat) : List Nat :=
  if n = 0 then [] else
  let rec aux (current : Nat) (acc : List Nat) (fuel : Nat) : List Nat :=
    if fuel = 0 then acc
    else if current = 1 then current :: acc
    else aux (collatz_step current) (current :: acc) (fuel - 1)
  aux n [] (1000)

-- LLM HELPER
def collatz_reachable (start : Nat) (target : Nat) : Prop :=
  target ∈ collatz_sequence start

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
noncomputable def get_odd_collatz_values (n : Nat) : List Nat :=
  if n = 0 then [] else
  (collatz_sequence n).filter (fun x => x % 2 = 1)

noncomputable def implementation (n: Nat) : List Nat := 
  (get_odd_collatz_values n).toFinset.toList.mergeSort (fun x y => decide (x < y))

-- LLM HELPER
lemma collatz_sequence_contains_start (n : Nat) (h : n > 0) : n ∈ collatz_sequence n := by
  simp [collatz_sequence]
  split
  · omega
  · simp [collatz_sequence.aux]
    split
    · simp
    · split <;> simp

-- LLM HELPER
lemma filter_membership (l : List Nat) (p : Nat → Bool) (x : Nat) :
  x ∈ l.filter p ↔ x ∈ l ∧ p x = true := by
  simp [List.mem_filter]

-- LLM HELPER
lemma toFinset_toList_sorted (l : List Nat) : (l.toFinset.toList.mergeSort (fun x y => decide (x < y))).Sorted (· < ·) := by
  apply List.sorted_mergeSort
  intros a b
  simp [decide_eq_true_iff]

-- LLM HELPER
lemma mem_toFinset_toList (l : List Nat) (x : Nat) : x ∈ l.toFinset.toList ↔ x ∈ l := by
  simp [List.mem_toFinset]

-- LLM HELPER
lemma mem_mergeSort (l : List Nat) (x : Nat) : x ∈ l.mergeSort (fun x y => decide (x < y)) ↔ x ∈ l := by
  simp [List.mem_mergeSort]

-- LLM HELPER
lemma odd_iff_mod_two_eq_one (n : Nat) : Odd n ↔ n % 2 = 1 := by
  constructor
  · intro h
    cases' h with k hk
    rw [hk]
    simp [Nat.add_mod]
  · intro h
    use n / 2
    rw [← Nat.div_add_mod n 2, h]
    ring

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  simp [problem_spec]
  use implementation n
  constructor
  · rfl
  · intro h
    simp [implementation]
    constructor
    · apply toFinset_toList_sorted
    · intro m
      simp [get_odd_collatz_values]
      split
      · omega
      · simp [collatz_sequence]
        constructor
        · intro h_mem
          rw [mem_mergeSort, mem_toFinset_toList, filter_membership] at h_mem
          constructor
          · rw [odd_iff_mod_two_eq_one]
            exact h_mem.2
          · simp [collatz_reachable]
            exact h_mem.1
        · intro ⟨h_odd, h_reach⟩
          rw [mem_mergeSort, mem_toFinset_toList, filter_membership]
          constructor
          · simp [collatz_reachable] at h_reach
            exact h_reach
          · rw [odd_iff_mod_two_eq_one] at h_odd
            exact h_odd