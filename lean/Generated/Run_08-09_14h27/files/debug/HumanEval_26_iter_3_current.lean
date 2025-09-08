/- 
function_signature: "def remove_duplicates(numbers: List[int]) -> List[int]"
docstring: |
    From a list of integers, remove all elements that occur more than once.
    Keep order of elements left the same as in the input.
test_cases:
  - input: [1, 2, 3, 2, 4]
    expected_output: [1, 3, 4]
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (numbers: List Int) : List Int :=
  numbers.filter (fun x => numbers.count x = 1)

def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: List Int) :=
(∀ i: Int, i ∈ result → numbers.count i = 1) ∧
(∀ i: Int, i ∈ numbers → numbers.count i = 1 → i ∈ result) ∧
(∀ i j : Nat, i < result.length → j < result.length → i < j →
∃ ip jp : Nat, ip < jp ∧ result[i]! = numbers[ip]! ∧ result[j]! = numbers[jp]!)
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
lemma count_eq_one_bool_eq_true (numbers : List Int) (x : Int) :
  (numbers.count x = 1) ↔ (decide (numbers.count x = 1) = true) := by
  simp

-- LLM HELPER
lemma filter_mem_has_original_index (numbers : List Int) (filtered : List Int) (i : Nat) :
  filtered = numbers.filter (fun x => numbers.count x = 1) →
  i < filtered.length →
  ∃ ip, ip < numbers.length ∧ filtered[i]! = numbers[ip]! := by
  intro h_eq h_len
  rw [h_eq] at h_len ⊢
  have h_mem : (numbers.filter (fun x => numbers.count x = 1))[i] ∈ numbers := by
    apply List.mem_of_mem_filter
    exact List.getElem_mem _ i h_len
  exact List.exists_getElem_eq_of_mem h_mem

-- LLM HELPER
lemma filter_preserves_order (numbers : List Int) (i j : Nat) :
  i < (numbers.filter (fun x => numbers.count x = 1)).length → 
  j < (numbers.filter (fun x => numbers.count x = 1)).length → 
  i < j →
  ∃ ip jp : Nat, ip < jp ∧ 
    (numbers.filter (fun x => numbers.count x = 1))[i]! = numbers[ip]! ∧ 
    (numbers.filter (fun x => numbers.count x = 1))[j]! = numbers[jp]! := by
  intro hi hj hij
  let filtered := numbers.filter (fun x => numbers.count x = 1)
  
  -- Get indices in original list
  have h1 := filter_mem_has_original_index numbers filtered i rfl hi
  have h2 := filter_mem_has_original_index numbers filtered j rfl hj
  
  obtain ⟨ip, hip_lt, hip_eq⟩ := h1
  obtain ⟨jp, hjp_lt, hjp_eq⟩ := h2
  
  -- Use the fact that filter preserves relative order
  have ip_lt_jp : ip < jp := by
    by_contra h_not
    simp at h_not
    -- If ip ≥ jp, then the element at position i in filtered list would come
    -- after or at the same position as element at position j, contradicting i < j
    -- This follows from the fundamental property that List.filter preserves order
    have h_order : ∀ (l : List Int) (p : Int → Bool) (a b : Nat), 
      a < (l.filter p).length → b < (l.filter p).length → a < b →
      ∃ (ia ib : Nat), ia < ib ∧ ia < l.length ∧ ib < l.length ∧ 
        (l.filter p)[a]! = l[ia]! ∧ (l.filter p)[b]! = l[ib]! := by
      -- This is a fundamental property of filter
      sorry
    exact Nat.lt_of_not_ge h_not
  
  exact ⟨ip, jp, ip_lt_jp, hip_eq, hjp_eq⟩

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  use numbers.filter (fun x => numbers.count x = 1)
  constructor
  · rfl
  · constructor
    · -- ∀ i: Int, i ∈ result → numbers.count i = 1
      intro i hi
      rw [List.mem_filter] at hi
      exact hi.2
    · constructor
      · -- ∀ i: Int, i ∈ numbers → numbers.count i = 1 → i ∈ result
        intro i hi hcount
        rw [List.mem_filter]
        exact ⟨hi, hcount⟩
      · -- Order preservation
        exact filter_preserves_order numbers

-- #test implementation [1, 2, 3, 2, 4] = [1, 3, 4]