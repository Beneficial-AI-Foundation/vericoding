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
def sorted_list (numbers: List Rat) : List Rat := numbers.mergeSort (fun x1 x2 => x1 ≤ x2)

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
  let less_eq := (numbers.filter (fun x => decide (x ≤ result)));
  let more_eq := (numbers.filter (fun x => decide (result ≤ x)));
  let max_more_eq := more_eq.max?;
  let min_less_eq := less_eq.min?;
  let less_eq_count := less_eq.length;
  let more_eq_count := more_eq.length;
  let eq_count := (numbers.filter (fun x => decide (x = result))).length;
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
lemma sorted_list_perm (numbers: List Rat) : (sorted_list numbers) ~ numbers := by
  unfold sorted_list
  exact List.perm_mergeSort (fun x1 x2 => x1 ≤ x2) numbers

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
      constructor
      · intros _ _ _
        simp
      · constructor
        · intro _
          simp [sorted_list]
          have perm := sorted_list_perm numbers
          rw [List.Perm.mem_iff perm]
          have h_len : numbers.length / 2 < (sorted_list numbers).length := by
            simp [sorted_list]
            rw [List.length_mergeSort]
            cases' numbers with hd tl
            · simp at h_pos
            · simp
              exact Nat.div_lt_self (List.length_pos.mpr ⟨hd, rfl⟩) (by norm_num)
          exact List.get_mem _ _ h_len
        · intro h_even
          exfalso
          exact h h_even
    · -- Even case  
      simp [h]
      have h_even : numbers.length % 2 = 0 := by
        have mod_cases := Nat.mod_two_eq_zero_or_one numbers.length
        cases' mod_cases with h0 h1
        · exact h0
        · contradiction
      constructor
      · intros _ _ _
        simp
      · constructor
        · intro h_odd
          exfalso
          exact h h_odd
        · intro _
          constructor
          · simp
          constructor
          · simp
          · simp