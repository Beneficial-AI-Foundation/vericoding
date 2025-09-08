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
def sorted_list (numbers: List Rat) : List Rat := numbers.mergeSort (· ≤ ·)

def implementation (numbers: List Rat) : Rat :=
  if numbers.length = 0 then 0
  else
    let sorted := sorted_list numbers
    let n := numbers.length
    if n % 2 = 1 then
      sorted[n / 2]!
    else
      let mid1 := sorted[n / 2 - 1]!
      let mid2 := sorted[n / 2]!
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
  exact List.sorted_mergeSort (· ≤ ·) numbers

-- LLM HELPER
lemma sorted_list_perm (numbers: List Rat) : (sorted_list numbers) ~ numbers := by
  unfold sorted_list
  exact List.perm_mergeSort (· ≤ ·) numbers

-- LLM HELPER
lemma sorted_list_length (numbers: List Rat) : (sorted_list numbers).length = numbers.length := by
  exact List.Perm.length_eq (sorted_list_perm numbers)

-- LLM HELPER
lemma median_property_odd (numbers: List Rat) (h_pos: 0 < numbers.length) (h_odd: numbers.length % 2 = 1) :
  let sorted := sorted_list numbers
  let result := sorted[numbers.length / 2]!
  result ∈ numbers ∧ 
  (numbers.filter (fun x => x ≤ result)).length ≥ (numbers.length + 1) / 2 ∧
  (numbers.filter (fun x => result ≤ x)).length ≥ (numbers.length + 1) / 2 := by
  simp only [sorted_list]
  have perm := sorted_list_perm numbers
  have mem : sorted_list numbers [numbers.length / 2]! ∈ numbers := by
    rw [sorted_list_length] at h_pos
    have h_valid : numbers.length / 2 < (sorted_list numbers).length := by
      rw [sorted_list_length]
      rw [Nat.div_lt_iff_lt_mul_right (by norm_num : 0 < 2)]
      rw [← h_odd]
      exact Nat.mod_add_div numbers.length 2 ▸ Nat.le_add_left 1 _
    exact List.Perm.mem_iff perm.symm ▸ List.get_mem _ _ h_valid
  exact ⟨mem, by simp, by simp⟩

-- LLM HELPER  
lemma median_property_even (numbers: List Rat) (h_pos: 0 < numbers.length) (h_even: numbers.length % 2 = 0) :
  let sorted := sorted_list numbers
  let mid1 := sorted[numbers.length / 2 - 1]!
  let mid2 := sorted[numbers.length / 2]!
  let result := (mid1 + mid2) / 2
  (numbers.filter (fun x => x ≤ result)).length ≥ numbers.length / 2 ∧
  (numbers.filter (fun x => result ≤ x)).length ≥ numbers.length / 2 ∧
  (numbers.filter (fun x => x ≤ result)).max? = some mid1 ∧
  (numbers.filter (fun x => result ≤ x)).min? = some mid2 := by
  simp only [sorted_list]
  exact ⟨by simp, by simp, by simp, by simp⟩

-- LLM HELPER
lemma even_case_helper (numbers: List Rat) (h: ¬numbers.length % 2 = 1) : numbers.length % 2 = 0 := by
  have mod_cases := Nat.mod_two_eq_zero_or_one numbers.length
  cases' mod_cases with h0 h1
  · exact h0
  · contradiction

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
      exact ⟨fun _ _ _ => ⟨by simp, by simp⟩, ⟨fun _ => med_prop.1, fun h_even => False.elim (h h_even)⟩⟩
    · -- Even case  
      simp [h]
      have h_even := even_case_helper numbers h
      have med_prop := median_property_even numbers h_pos h_even
      exact ⟨fun _ _ _ => ⟨by simp, by simp⟩, ⟨fun h_odd => False.elim (h h_odd), fun _ => ⟨by simp, by simp, by simp⟩⟩⟩

-- #test implementation [3, 1, 2, 4, 5] = 3
-- #test implementation [-10, 4, 6, 1000, 10, 20] = 15.0