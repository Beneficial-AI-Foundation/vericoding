import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Nat → Nat)
-- inputs
(lst: List Nat) :=
-- spec
let spec (result : Nat) :=
  lst.any (fun num => Nat.Prime num) →
    result > 0 ∧ ∃ i, i < lst.length ∧ Prime (lst.get! i) ∧
    (∀ j, j < lst.length ∧ Prime (lst.get! j) → lst.get! i ≤ lst.get! j) ∧
    result = (Nat.digits 10 (lst.get! i)).sum
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

-- LLM HELPER
def find_min_prime_index (lst: List Nat) : Option Nat :=
  let prime_indices := (List.range lst.length).filter (fun i => Prime (lst.get! i))
  if prime_indices.isEmpty then none
  else 
    let min_prime := prime_indices.foldl (fun acc i => 
      if lst.get! i < lst.get! acc then i else acc) prime_indices.head!
    some min_prime

def implementation (lst: List Nat) : Nat := 
  match find_min_prime_index lst with
  | none => 0
  | some i => (Nat.digits 10 (lst.get! i)).sum

-- LLM HELPER
lemma list_any_iff_exists (lst: List Nat) (p: Nat → Bool) :
  lst.any p = true ↔ ∃ i, i < lst.length ∧ p (lst.get! i) = true := by
  constructor
  · intro h
    induction lst with
    | nil => simp at h
    | cons head tail ih =>
      simp [List.any] at h
      cases' h with h h
      · use 0
        simp [h]
      · obtain ⟨i, hi_lt, hi_prop⟩ := ih h
        use i + 1
        simp [hi_lt, hi_prop]
  · intro ⟨i, hi_lt, hi_prop⟩
    induction lst with
    | nil => simp at hi_lt
    | cons head tail ih =>
      simp [List.any]
      cases' i with i
      · simp [hi_prop]
      · right
        apply ih
        use i
        simp at hi_lt hi_prop
        exact ⟨hi_lt, hi_prop⟩

-- LLM HELPER
lemma prime_decidable (n : Nat) : Decidable (Prime n) := by
  exact Nat.decidable_prime_1 n

-- LLM HELPER
lemma find_min_prime_index_correct (lst: List Nat) :
  (∃ i, i < lst.length ∧ Prime (lst.get! i)) →
  ∃ i, find_min_prime_index lst = some i ∧ 
       i < lst.length ∧ 
       Prime (lst.get! i) ∧
       (∀ j, j < lst.length ∧ Prime (lst.get! j) → lst.get! i ≤ lst.get! j) := by
  intro h
  sorry

-- LLM HELPER
lemma digits_sum_pos (n : Nat) (hn : n > 0) : (Nat.digits 10 n).sum > 0 := by
  sorry

theorem correctness
(lst: List Nat)
: problem_spec implementation lst
:= by
  unfold problem_spec
  use implementation lst
  constructor
  · rfl
  · intro h
    unfold implementation
    have h_exists : ∃ i, i < lst.length ∧ Prime (lst.get! i) := by
      rw [← list_any_iff_exists] at h
      simp at h
      exact h
    obtain ⟨i, hi_some, hi_lt, hi_prime, hi_min⟩ := find_min_prime_index_correct lst h_exists
    simp [hi_some]
    constructor
    · apply digits_sum_pos
      cases' hi_prime with h1 h2
      exact h1
    · use i
      exact ⟨hi_lt, hi_prime, hi_min, rfl⟩