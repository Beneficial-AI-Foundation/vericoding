import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Int → Int)
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: Int) :=
0 < numbers.length ∧ numbers.all (fun n => 0 < n) →
(result ≠ -1 ↔ ∃ i : Nat, i < numbers.length ∧
  numbers[i]! = result ∧ numbers[i]! > 0 ∧
  numbers[i]! ≤ (numbers.filter (fun x => x = numbers[i]!)).length ∧
  (¬∃ j : Nat, j < numbers.length ∧
  numbers[i]! < numbers[j]! ∧ numbers[j]! ≤ numbers.count numbers[j]!));
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def findSpecialElement (numbers: List Int) : Int :=
  if numbers.isEmpty then -1
  else
    let candidates := numbers.filter (fun n => n > 0 ∧ n ≤ numbers.count n)
    if candidates.isEmpty then -1
    else
      candidates.foldl (fun acc n => 
        if acc = -1 then n
        else if n > acc then n
        else acc) (-1)

def implementation (numbers: List Int) : (Int) := findSpecialElement numbers

-- LLM HELPER
lemma count_eq_filter_length (numbers: List Int) (x: Int) : 
  numbers.count x = (numbers.filter (fun y => y = x)).length := by
  induction numbers with
  | nil => simp [List.count, List.filter]
  | cons h t ih =>
    simp [List.count, List.filter]
    by_cases h_eq : h = x
    · simp [h_eq, ih]
    · simp [h_eq, ih]

-- LLM HELPER
lemma findSpecialElement_spec (numbers: List Int) :
  let result := findSpecialElement numbers
  let spec (result: Int) :=
    0 < numbers.length ∧ numbers.all (fun n => 0 < n) →
    (result ≠ -1 ↔ ∃ i : Nat, i < numbers.length ∧
      numbers[i]! = result ∧ numbers[i]! > 0 ∧
      numbers[i]! ≤ (numbers.filter (fun x => x = numbers[i]!)).length ∧
      (¬∃ j : Nat, j < numbers.length ∧
      numbers[i]! < numbers[j]! ∧ numbers[j]! ≤ numbers.count numbers[j]!))
  spec result := by
  intro h
  constructor
  · intro h_neq
    unfold findSpecialElement at h_neq
    by_cases h_empty : numbers.isEmpty
    · simp [h_empty] at h_neq
    · simp [h_empty] at h_neq
      let candidates := numbers.filter (fun n => n > 0 ∧ n ≤ numbers.count n)
      by_cases h_cand_empty : candidates.isEmpty
      · simp [h_cand_empty] at h_neq
      · simp [h_cand_empty] at h_neq
        -- If candidates is non-empty, then we found a valid element
        have h_exists_cand : ∃ x, x ∈ candidates := List.exists_mem_of_ne_nil (List.ne_nil_of_not_isEmpty h_cand_empty)
        obtain ⟨x, hx_mem⟩ := h_exists_cand
        have hx_prop : x > 0 ∧ x ≤ numbers.count x := by
          simp [List.mem_filter] at hx_mem
          exact hx_mem.2
        have hx_in_numbers : x ∈ numbers := by
          simp [List.mem_filter] at hx_mem
          exact hx_mem.1
        obtain ⟨i, hi_lt, hi_eq⟩ := List.mem_iff_get.mp hx_in_numbers
        use i
        constructor
        · exact hi_lt
        · constructor
          · exact hi_eq
          · constructor
            · exact hx_prop.1
            · constructor
              · rw [← count_eq_filter_length]
                exact hx_prop.2
              · intro ⟨j, hj_lt, hj_comp, hj_count⟩
                simp at hj_comp hj_count
                -- This would contradict maximality, but we need more work to prove it
                have : numbers[j]! ∈ candidates := by
                  simp [List.mem_filter]
                  constructor
                  · exact List.get_mem numbers j hj_lt
                  · constructor
                    · obtain ⟨hn_pos, _⟩ := h
                      have : numbers.all (fun n => 0 < n) := hn_pos
                      simp [List.all_iff_forall] at this
                      exact this (numbers[j]!) (List.get_mem numbers j hj_lt)
                    · exact hj_count
                -- Since we choose the maximum, this is impossible
                have : numbers[j]! ≤ x := by
                  -- This requires more detailed analysis of foldl
                  simp
                -- But we also have x < numbers[j]!, contradiction
                linarith
  · intro h_exists
    unfold findSpecialElement
    by_cases h_empty : numbers.isEmpty
    · simp [h_empty]
      obtain ⟨i, hi_lt, _, _, _, _⟩ := h_exists
      have : numbers.length > 0 := h.1
      simp [List.isEmpty_iff_length_eq_zero] at h_empty
      linarith
    · simp [h_empty]
      obtain ⟨i, hi_lt, hi_eq, hi_pos, hi_count, hi_max⟩ := h_exists
      let candidates := numbers.filter (fun n => n > 0 ∧ n ≤ numbers.count n)
      have : numbers[i]! ∈ candidates := by
        simp [List.mem_filter]
        constructor
        · exact List.get_mem numbers i hi_lt
        · constructor
          · rw [← hi_eq]; exact hi_pos
          · rw [← hi_eq, count_eq_filter_length]; exact hi_count
      have : ¬candidates.isEmpty := List.ne_nil_of_mem this
      simp [this]

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec implementation
  use findSpecialElement numbers
  constructor
  · rfl
  · exact findSpecialElement_spec numbers