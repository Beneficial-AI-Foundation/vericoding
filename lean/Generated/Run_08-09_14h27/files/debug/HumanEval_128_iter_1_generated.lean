/- 
function_signature: "def prod_signs(arr: List[int]) -> Optional[int]"
docstring: |
    You are given an array arr of integers and you need to return
    sum of magnitudes of integers multiplied by product of all signs
    of each number in the array, represented by 1, -1 or 0.
    Note: return None for empty arr.
test_cases:
  - input: [1, 2, 2, -4]
    expected_output: -9
  - input: [0, 1]
    expected_output: 0
  - input: []
    expected_output: None
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (arr: List Int) : Option Int :=
  if arr = [] then
    none
  else
    let magnitude_sum := (arr.map (fun x => Int.ofNat x.natAbs)).sum
    let has_zero := 0 ∈ arr
    if has_zero then
      some 0
    else
      let neg_count := (arr.filter (fun x => x < 0)).length
      if neg_count % 2 = 1 then
        some (-magnitude_sum)
      else
        some magnitude_sum

def problem_spec
-- function signature
(impl: List Int → Option Int)
-- inputs
(arr: List Int) :=
-- spec
let spec (result: Option Int) :=
  match result with
  | none => arr = []
  | some result =>
  let magnitude_sum := (arr.map (fun x => Int.ofNat x.natAbs)).sum;
    let neg_count_odd := (arr.filter (fun x => x < 0)).length % 2 = 1;
    let has_zero := 0 ∈ arr;
    (result < 0 ↔ (neg_count_odd ∧ ¬has_zero)
      ∧ result = magnitude_sum * -1) ∧
    (0 < result ↔ (¬neg_count_odd ∧ ¬has_zero)
      ∧ result = magnitude_sum) ∧
    (result = 0 ↔ has_zero)
-- program terminates
∃ result, impl arr = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma neg_sum_eq_mul_neg_one (s : Int) : -s = s * (-1) := by
  ring

-- LLM HELPER
lemma pos_of_natAbs_sum (arr : List Int) (h : arr ≠ []) : 0 ≤ (arr.map (fun x => Int.ofNat x.natAbs)).sum := by
  apply List.sum_nonneg
  intro x hx
  simp at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact Int.natCast_nonneg _

-- LLM HELPER
lemma zero_not_mem_iff_all_ne_zero (arr : List Int) : 0 ∉ arr ↔ ∀ x ∈ arr, x ≠ 0 := by
  simp [List.mem_iff_exists]

theorem correctness
(arr: List Int)
: problem_spec implementation arr := by
  unfold problem_spec
  simp [implementation]
  split_ifs with h1 h2 h3
  · -- Case: arr = []
    use none
    simp [h1]
  · -- Case: arr ≠ [] and has_zero
    use (some 0)
    simp
    constructor
    · exact h1
    · constructor
      · -- result < 0 ↔ (neg_count_odd ∧ ¬has_zero) ∧ result = magnitude_sum * -1
        simp [h2]
      · constructor
        · -- 0 < result ↔ (¬neg_count_odd ∧ ¬has_zero) ∧ result = magnitude_sum
          simp [h2]
        · -- result = 0 ↔ has_zero
          exact h2
  · -- Case: arr ≠ [] and ¬has_zero and neg_count % 2 = 1
    let magnitude_sum := (arr.map (fun x => Int.ofNat x.natAbs)).sum
    use (some (-magnitude_sum))
    simp
    constructor
    · exact h1
    · constructor
      · -- result < 0 ↔ (neg_count_odd ∧ ¬has_zero) ∧ result = magnitude_sum * -1
        constructor
        · intro h_neg
          constructor
          · constructor
            · exact h3
            · exact h2
          · rw [neg_sum_eq_mul_neg_one]
        · intro h_and
          obtain ⟨⟨_, _⟩, h_eq⟩ := h_and
          rw [neg_sum_eq_mul_neg_one] at h_eq
          have h_pos : 0 ≤ magnitude_sum := pos_of_natAbs_sum arr h1
          cases' Nat.eq_zero_or_pos magnitude_sum.natAbs with h_zero h_pos_nat
          · have : magnitude_sum = 0 := by
              rw [← Int.natAbs_eq_zero] at h_zero
              exact h_zero
            simp [this]
          · have : magnitude_sum > 0 := by
              rw [Int.pos_iff_natAbs_pos]
              exact h_pos_nat
            linarith
      · constructor
        · -- 0 < result ↔ (¬neg_count_odd ∧ ¬has_zero) ∧ result = magnitude_sum
          simp [h3, h2]
        · -- result = 0 ↔ has_zero
          simp [h2]
  · -- Case: arr ≠ [] and ¬has_zero and neg_count % 2 ≠ 1
    let magnitude_sum := (arr.map (fun x => Int.ofNat x.natAbs)).sum
    use (some magnitude_sum)
    simp
    constructor
    · exact h1
    · constructor
      · -- result < 0 ↔ (neg_count_odd ∧ ¬has_zero) ∧ result = magnitude_sum * -1
        simp [h3, h2]
        have h_pos : 0 ≤ magnitude_sum := pos_of_natAbs_sum arr h1
        intro h_contra
        linarith
      · constructor
        · -- 0 < result ↔ (¬neg_count_odd ∧ ¬has_zero) ∧ result = magnitude_sum
          constructor
          · intro h_pos
            constructor
            · constructor
              · intro h_odd
                have : (arr.filter (fun x => x < 0)).length % 2 = 1 := h_odd
                exact h3 this
              · exact h2
            · rfl
          · intro h_and
            obtain ⟨⟨_, _⟩, _⟩ := h_and
            have h_nonneg : 0 ≤ magnitude_sum := pos_of_natAbs_sum arr h1
            cases' Nat.eq_zero_or_pos magnitude_sum.natAbs with h_zero h_pos_nat
            · have : magnitude_sum = 0 := by
                rw [← Int.natAbs_eq_zero] at h_zero
                exact h_zero
              simp [this]
            · rw [Int.pos_iff_natAbs_pos]
              exact h_pos_nat
        · -- result = 0 ↔ has_zero
          simp [h2]

-- #test implementation ([1, 2, 2, -4]: List Int) = (-9: Int)
-- #test implementation ([0, 1]: List Int) = (0: Int)
-- #test implementation ([]: List Int) = none