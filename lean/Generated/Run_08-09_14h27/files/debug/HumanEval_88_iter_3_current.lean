/- 
function_signature: "def sort_array(lst : list(int)) -> list(int)"
docstring: |
    """
    Given an array of non-negative integers, return a copy of the given array after sorting,
    you will sort the given array in ascending order if the sum( first index value, last index value) is odd,
    or sort it in descending order if the sum( first index value, last index value) is even.
    Note(George): I have elected to ignore the copy part.
test_cases:
  - input: []
    output: []
  - input: [5]
    output: [5]
  - input: [2, 4, 3, 0, 1, 5]
    output: [0, 1, 2, 3, 4, 5]
  - input: [2, 4, 3, 0, 1, 5, 6]
    output: [6, 5, 4, 3, 2, 1, 0]
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (lst: List Nat) : List Nat :=
  if lst.length = 0 then []
  else if (lst.head! + lst.getLast!) % 2 = 1 then
    lst.mergeSort (fun a b => a ≤ b)
  else
    lst.mergeSort (fun a b => a ≥ b)

def problem_spec
-- function signature
(implementation: List Nat → List Nat)
-- inputs
(lst: List Nat) :=
-- spec
let spec (result : List Nat) :=
  lst.length > 0 →
  result.length = lst.length ∧
  (∀ i, i < result.length →
    result[i]! ∈ lst ∧
    lst[i]! ∈ result ∧
    result.count (lst[i]!) = lst.count (lst[i]!)) ∧
  (lst.head! + lst.getLast!) ≡ 1 [MOD 2] →
    result.Sorted (fun a b => a ≤ b) ∧
  (lst.head! + lst.getLast!) ≡ 0 [MOD 2] →
    result.Sorted (fun a b => a ≥ b)
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

-- LLM HELPER
lemma list_perm_count {α : Type*} [DecidableEq α] {l₁ l₂ : List α} (h : l₁ ~ l₂) :
  ∀ a, l₁.count a = l₂.count a := by
  intro a
  exact List.Perm.count_eq h

-- LLM HELPER
lemma list_perm_mem {α : Type*} {l₁ l₂ : List α} (h : l₁ ~ l₂) :
  ∀ a, a ∈ l₁ ↔ a ∈ l₂ := by
  intro a
  exact List.Perm.mem_iff h

-- LLM HELPER
lemma nat_mod_two_cases (n : Nat) : n % 2 = 0 ∨ n % 2 = 1 := by
  have : n % 2 < 2 := Nat.mod_lt n (by norm_num)
  omega

-- LLM HELPER
lemma nat_mod_eq_zmod_eq (a b : Nat) : a % b = 1 ↔ a ≡ 1 [MOD b] := by
  rw [ZMod.nat_coe_eq_nat_coe_iff]
  simp [ZMod.int_coe_mod]

-- LLM HELPER  
lemma nat_mod_eq_zmod_eq_zero (a b : Nat) : a % b = 0 ↔ a ≡ 0 [MOD b] := by
  rw [ZMod.nat_coe_eq_nat_coe_iff]
  simp [ZMod.int_coe_mod]

theorem correctness
(lst: List Nat)
: problem_spec implementation lst
:= by
  unfold problem_spec
  unfold implementation
  by_cases h : lst.length = 0
  · -- Empty list case
    simp [h]
    use []
    simp
  · -- Non-empty list case
    simp [h]
    cases' nat_mod_two_cases (lst.head! + lst.getLast!) with h_even h_odd
    · -- Sum is even (mod 2 = 0)
      simp [h_even]
      use lst.mergeSort (fun a b => a ≥ b)
      constructor
      · rfl
      · intro h_pos
        constructor
        · exact List.length_mergeSort lst (fun a b => a ≥ b)
        · constructor
          · intro i hi
            constructor
            · rw [List.getElem_mergeSort]
              exact List.getElem_mem lst i (by rw [← List.length_mergeSort] at hi; exact hi)
            · constructor
              · have perm := List.mergeSort_perm lst (fun a b => a ≥ b)
                rw [List.getElem_mergeSort] at hi ⊢
                have mem := List.getElem_mem (lst.mergeSort (fun a b => a ≥ b)) i hi
                exact (list_perm_mem perm.symm (lst[i]!)).mp (List.getElem_mem lst i (by rw [List.length_mergeSort] at hi; exact hi))
              · have perm := List.mergeSort_perm lst (fun a b => a ≥ b)
                exact list_perm_count perm (lst[i]!)
          · constructor
            · intro h_odd_contr
              rw [← nat_mod_eq_zmod_eq] at h_odd_contr
              rw [h_even] at h_odd_contr
              norm_num at h_odd_contr
            · intro h_even_contr
              rw [← nat_mod_eq_zmod_eq_zero] at h_even_contr
              rw [h_even] at h_even_contr
              exact List.mergeSort_sorted lst (fun a b => a ≥ b) ge_trans
    · -- Sum is odd (mod 2 = 1)
      simp [h_odd]
      use lst.mergeSort (fun a b => a ≤ b)
      constructor
      · rfl
      · intro h_pos
        constructor
        · exact List.length_mergeSort lst (fun a b => a ≤ b)
        · constructor
          · intro i hi
            constructor
            · rw [List.getElem_mergeSort]
              exact List.getElem_mem lst i (by rw [← List.length_mergeSort] at hi; exact hi)
            · constructor
              · have perm := List.mergeSort_perm lst (fun a b => a ≤ b)
                rw [List.getElem_mergeSort] at hi ⊢
                have mem := List.getElem_mem (lst.mergeSort (fun a b => a ≤ b)) i hi
                exact (list_perm_mem perm.symm (lst[i]!)).mp (List.getElem_mem lst i (by rw [List.length_mergeSort] at hi; exact hi))
              · have perm := List.mergeSort_perm lst (fun a b => a ≤ b)
                exact list_perm_count perm (lst[i]!)
          · constructor
            · intro h_odd_contr
              rw [← nat_mod_eq_zmod_eq] at h_odd_contr
              rw [h_odd] at h_odd_contr
              exact List.mergeSort_sorted lst (fun a b => a ≤ b) le_trans
            · intro h_even_contr
              rw [← nat_mod_eq_zmod_eq_zero] at h_even_contr
              rw [h_odd] at h_even_contr
              norm_num at h_even_contr

-- #test implementation [] = []
-- #test implementation [5] = [5]
-- #test implementation [2, 4, 3, 0, 1, 5] = [0, 1, 2, 3, 4, 5]
-- #test implementation [2, 4, 3, 0, 1, 5, 6] = [6, 5, 4, 3, 2, 1, 0]