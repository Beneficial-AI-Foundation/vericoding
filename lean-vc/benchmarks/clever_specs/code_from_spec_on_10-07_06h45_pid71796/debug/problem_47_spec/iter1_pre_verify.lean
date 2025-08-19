import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic

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
def median_helper (numbers: List Rat) : Rat :=
  if numbers.length = 0 then 0 else
  let sorted := numbers.toArray.qsort (· ≤ ·)
  let n := sorted.size
  if n % 2 = 1 then
    sorted[n / 2]!
  else
    (sorted[n / 2 - 1]! + sorted[n / 2]!) / 2

def implementation (numbers: List Rat) : Rat := median_helper numbers

-- LLM HELPER
lemma filter_le_ge_cover (numbers: List Rat) (result: Rat) :
  let less_eq := (numbers.filter (fun x => x ≤ result))
  let more_eq := (numbers.filter (fun x => result ≤ x))
  let eq_count := (numbers.filter (fun x => x = result)).length
  less_eq.length + more_eq.length - eq_count = numbers.length := by
  simp only [List.length_filter]
  have h : ∀ x ∈ numbers, (x ≤ result ∨ result < x) := fun x _ => le_or_lt x result
  have h2 : ∀ x ∈ numbers, (x = result → x ≤ result ∧ result ≤ x) := fun x _ hx => by
    rw [hx]; exact ⟨le_refl _, le_refl _⟩
  simp only [Nat.cast_sum, Finset.sum_boole]
  rw [← List.card_toFinset]
  simp only [List.toFinset_filter]
  sorry

-- LLM HELPER
lemma qsort_sorted (arr : Array Rat) : 
  let sorted := arr.qsort (· ≤ ·)
  ∀ i j, i < j → j < sorted.size → sorted[i]! ≤ sorted[j]! := by
  sorry

-- LLM HELPER
lemma qsort_mem_iff (arr : Array Rat) (x : Rat) :
  x ∈ arr.qsort (· ≤ ·) ↔ x ∈ arr := by
  sorry

-- LLM HELPER
lemma qsort_size (arr : Array Rat) : (arr.qsort (· ≤ ·)).size = arr.size := by
  sorry

-- LLM HELPER
lemma median_properties (numbers: List Rat) (h: 0 < numbers.length) :
  let result := median_helper numbers
  let less_eq := (numbers.filter (fun x => x ≤ result))
  let more_eq := (numbers.filter (fun x => result ≤ x))
  let max_more_eq := more_eq.max?
  let min_less_eq := less_eq.min?
  let less_eq_count := less_eq.length
  let more_eq_count := more_eq.length
  let eq_count := (numbers.filter (fun x => x = result)).length
  (less_eq_count + more_eq_count - eq_count = numbers.length →
  numbers.length ≤ 2 * less_eq_count →
  numbers.length ≤ 2 * more_eq_count) ∧
  ((numbers.length % 2 = 1 →
    result ∈ numbers) ∧
    (numbers.length % 2 = 0 → max_more_eq.isSome ∧
    min_less_eq.isSome ∧
    2 * result = max_more_eq.get! + min_less_eq.get!)) := by
  sorry

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers := by
  unfold problem_spec implementation
  use median_helper numbers
  constructor
  · rfl
  · intro h
    exact median_properties numbers h