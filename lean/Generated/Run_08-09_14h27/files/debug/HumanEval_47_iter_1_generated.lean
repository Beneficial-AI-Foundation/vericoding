/- 
function_signature: "def median(numbers: List[float]) -> float"
docstring: |
    Return median of elements in the list l
test_cases:
  - input: [3, 1, 2, 4, 5]
    output: 3
  - input: [-10, 4, 6, 1000, 10, 20]
    output: 15.0
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def sorted_list (numbers: List Rat) : List Rat := numbers.toArray.qsort (· ≤ ·) |>.toList

def implementation (numbers: List Rat) : Rat :=
  if numbers.length = 0 then 0
  else
    let sorted := sorted_list numbers
    let n := numbers.length
    if n % 2 = 1 then
      sorted.get! (n / 2)
    else
      let mid1 := sorted.get! (n / 2 - 1)
      let mid2 := sorted.get! (n / 2)
      (mid1 + mid2) / 2

def problem_spec
-- function signature
(implementation: List Rat → Rat)
-- inputs
(numbers: List Rat) :=
-- spec
let spec (result: Rat) :=
  0 < numbers.length →
  let less_eq := (numbers.filter (fun x => x ≤ result));
  let more_eq := (numbers.filter (fun x => result ≤ x));
  let max_more_eq := more_eq.max?;
  let min_less_eq := less_eq.min?;
  let less_eq_count := less_eq.length;
  let more_eq_count := more_eq.length;
  let eq_count := (numbers.filter (fun x => x = result)).length;
  (less_eq_count + more_eq_count - eq_count = numbers.length →
  numbers.length ≤ 2 * less_eq_count →
  numbers.length ≤ 2 * more_eq_count) ∧
  ((numbers.length % 2 = 1 →
    result ∈ numbers) ∧
    (numbers.length % 2 = 0 → max_more_eq.isSome ∧
    min_less_eq.isSome ∧
    2 * result = max_more_eq.get! + min_less_eq.get!));
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
lemma sorted_list_sorted (numbers: List Rat) : (sorted_list numbers).Sorted (· ≤ ·) := by
  unfold sorted_list
  simp [Array.toList_toArray]
  apply Array.Sorted.toList
  apply Array.qsort_sorted

-- LLM HELPER
lemma sorted_list_perm (numbers: List Rat) : (sorted_list numbers) ~ numbers := by
  unfold sorted_list
  simp [Array.toList_toArray]
  apply Array.qsort_permutation

-- LLM HELPER
lemma sorted_list_length (numbers: List Rat) : (sorted_list numbers).length = numbers.length := by
  rw [List.Perm.length_eq (sorted_list_perm numbers)]

-- LLM HELPER
lemma median_property_odd (numbers: List Rat) (h_pos: 0 < numbers.length) (h_odd: numbers.length % 2 = 1) :
  let sorted := sorted_list numbers
  let result := sorted.get! (numbers.length / 2)
  result ∈ numbers ∧ 
  (numbers.filter (fun x => x ≤ result)).length ≥ (numbers.length + 1) / 2 ∧
  (numbers.filter (fun x => result ≤ x)).length ≥ (numbers.length + 1) / 2 := by
  sorry

-- LLM HELPER  
lemma median_property_even (numbers: List Rat) (h_pos: 0 < numbers.length) (h_even: numbers.length % 2 = 0) :
  let sorted := sorted_list numbers
  let mid1 := sorted.get! (numbers.length / 2 - 1)  
  let mid2 := sorted.get! (numbers.length / 2)
  let result := (mid1 + mid2) / 2
  (numbers.filter (fun x => x ≤ result)).length ≥ numbers.length / 2 ∧
  (numbers.filter (fun x => result ≤ x)).length ≥ numbers.length / 2 ∧
  (numbers.filter (fun x => x ≤ result)).max? = some mid1 ∧
  (numbers.filter (fun x => result ≤ x)).min? = some mid2 := by
  sorry

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  use implementation numbers
  constructor
  · rfl
  · intro h_pos
    unfold implementation
    simp [if_neg (ne_of_gt h_pos)]
    by_cases h : numbers.length % 2 = 1
    · -- Odd case
      simp [h]
      have med_prop := median_property_odd numbers h_pos h
      sorry
    · -- Even case  
      simp [h]
      have med_prop := median_property_even numbers h_pos (Nat.mod_two_eq_zero_or_one numbers.length ▸ Or.resolve_left (Nat.mod_two_eq_zero_or_one numbers.length) h)
      sorry

-- #test implementation [3, 1, 2, 4, 5] = 3
-- #test implementation [-10, 4, 6, 1000, 10, 20] = 15.0