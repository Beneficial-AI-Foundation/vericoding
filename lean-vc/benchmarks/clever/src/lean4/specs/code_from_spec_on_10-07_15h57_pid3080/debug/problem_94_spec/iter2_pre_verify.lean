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
def find_smallest_prime_index (lst: List Nat) : Option Nat :=
  let prime_indices := lst.enum.filterMap (fun (i, n) => if Nat.Prime n then some i else none)
  if prime_indices.isEmpty then none
  else
    let min_prime := prime_indices.map (fun i => lst.get! i) |>.minimum?
    match min_prime with
    | none => none
    | some p => prime_indices.find? (fun i => lst.get! i = p)

def implementation (lst: List Nat) : Nat := 
  match find_smallest_prime_index lst with
  | none => 0
  | some i => (Nat.digits 10 (lst.get! i)).sum

-- LLM HELPER
lemma digits_sum_pos_of_prime {n : Nat} (h : Nat.Prime n) : (Nat.digits 10 n).sum > 0 := by
  have h_pos : n > 0 := Nat.Prime.pos h
  have h_ge_2 : n ≥ 2 := Nat.Prime.two_le h
  have digits_nonempty : (Nat.digits 10 n).length > 0 := by
    rw [Nat.digits_len]
    simp [Nat.log_pos_iff]
    exact h_ge_2
  have digits_all_pos : ∀ d ∈ Nat.digits 10 n, d > 0 := by
    intros d hd
    rw [Nat.mem_digits] at hd
    exact hd.2
  have sum_pos : (Nat.digits 10 n).sum > 0 := by
    apply List.sum_pos
    · exact digits_nonempty
    · exact digits_all_pos
  exact sum_pos

-- LLM HELPER
lemma find_smallest_prime_index_correct (lst: List Nat) (i : Nat) 
  (h : find_smallest_prime_index lst = some i) :
  i < lst.length ∧ Prime (lst.get! i) ∧
  (∀ j, j < lst.length ∧ Prime (lst.get! j) → lst.get! i ≤ lst.get! j) := by
  sorry

-- LLM HELPER
lemma any_prime_iff_exists_prime (lst: List Nat) :
  lst.any (fun num => Nat.Prime num) ↔ ∃ i, i < lst.length ∧ Prime (lst.get! i) := by
  sorry

theorem correctness
(lst: List Nat)
: problem_spec implementation lst
:= by
  unfold problem_spec
  simp only [implementation]
  cases h : find_smallest_prime_index lst with
  | none => 
    use 0
    constructor
    · rfl
    · intro has_prime
      exfalso
      rw [any_prime_iff_exists_prime] at has_prime
      obtain ⟨i, hi_bound, hi_prime⟩ := has_prime
      unfold find_smallest_prime_index at h
      simp at h
      sorry
  | some i =>
    use (Nat.digits 10 (lst.get! i)).sum
    constructor
    · rfl
    · intro has_prime
      have h_correct := find_smallest_prime_index_correct lst i h
      constructor
      · exact digits_sum_pos_of_prime h_correct.2.1
      · use i
        exact ⟨h_correct.1, h_correct.2.1, h_correct.2.2, rfl⟩