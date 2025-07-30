import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: List Int → Int → List Int)
(arr: List Int)
(k: Int) :=
let spec (result: List Int) :=
    1 ≤ arr.length → arr.length ≤ 1000 → arr.all (fun x => -1000 ≤ x ∧ x ≤ 1000) → 0 ≤ k → k ≤ arr.length →
    result.length = k ∧
    result.Sorted (· ≤ ·) ∧
    ∀ x ∈ result, x ∈ arr ∧

    let result_reversed := result.reverse; -- reverse to get last element
    match result_reversed with
    | [] => k = 0
    | max :: remaining_reversed =>
      arr.max? = some max ∧
      implementation (arr.erase max) (k-1) = (remaining_reversed.reverse)
∃ result, implementation arr k = result ∧
spec result

-- LLM HELPER
def getLargestK (arr: List Int) (k: Int) : List Int :=
  if k ≤ 0 then []
  else if arr.isEmpty then []
  else
    match arr.max? with
    | none => []
    | some max => 
      let remaining := arr.erase max
      let rest := getLargestK remaining (k - 1)
      rest ++ [max]

def implementation (arr: List Int) (k: Int) : List Int := getLargestK arr k

-- LLM HELPER
lemma getLargestK_length (arr: List Int) (k: Int) : 
  (getLargestK arr k).length = min k.natAbs arr.length := by
  sorry

-- LLM HELPER
lemma getLargestK_sorted (arr: List Int) (k: Int) : 
  (getLargestK arr k).Sorted (· ≤ ·) := by
  sorry

-- LLM HELPER
lemma getLargestK_mem (arr: List Int) (k: Int) : 
  ∀ x ∈ getLargestK arr k, x ∈ arr := by
  sorry

-- LLM HELPER
lemma getLargestK_max_property (arr: List Int) (k: Int) :
  k > 0 → arr.length > 0 →
  let result := getLargestK arr k
  let result_reversed := result.reverse
  match result_reversed with
  | [] => k = 0
  | max :: remaining_reversed =>
    arr.max? = some max ∧
    getLargestK (arr.erase max) (k-1) = (remaining_reversed.reverse) := by
  sorry

theorem correctness
(arr: List Int)
(k: Int)
: problem_spec implementation arr k := by
  unfold problem_spec implementation
  use getLargestK arr k
  constructor
  · rfl
  · intro h1 h2 h3 h4 h5
    constructor
    · rw [getLargestK_length]
      simp [Int.natAbs_of_nonneg h4]
      omega
    constructor
    · exact getLargestK_sorted arr k
    constructor
    · exact getLargestK_mem arr k
    · by_cases hk : k ≤ 0
      · simp [getLargestK, hk]
      · by_cases harr : arr.isEmpty
        · simp [getLargestK, harr]
          cases arr with
          | nil => simp at h1
          | cons => simp at harr
        · exact getLargestK_max_property arr k (by omega) (by cases arr; simp at h1; simp)