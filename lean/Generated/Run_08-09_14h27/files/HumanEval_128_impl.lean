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
    (result < 0 ↔ 
      ((List.filter (fun x => decide (x < 0)) arr).length % 2 = 1 ∧ 0 ∉ arr) ∧ 
      result = -((List.map (fun x => |x|) arr).sum)) ∧
    (0 < result ↔ 
      ((List.filter (fun x => decide (x < 0)) arr).length % 2 = 0 ∧ 0 ∉ arr) ∧ 
      result = (List.map (fun x => |x|) arr).sum) ∧
    (result = 0 ↔ 0 ∈ arr)
-- program terminates
∃ result, impl arr = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma zero_not_mem_iff_all_ne_zero (arr : List Int) : 0 ∉ arr ↔ ∀ x ∈ arr, x ≠ 0 := by
  constructor
  · intro h x hx h_eq
    rw [h_eq] at hx
    exact h hx
  · intro h hx
    exact h 0 hx rfl

-- LLM HELPER  
lemma abs_of_ofNat_natAbs (x : Int) : |x| = Int.ofNat x.natAbs := by
  exact Int.natAbs_abs x

-- LLM HELPER
lemma abs_pos_of_ne_zero (x : Int) (h : x ≠ 0) : 0 < |x| := by
  exact Int.abs_pos.mpr h

-- LLM HELPER
lemma sum_pos_of_nonempty_nonzero (arr : List Int) (h_nemp : arr ≠ []) (h_nozero : 0 ∉ arr) :
  0 < (List.map (fun x => |x|) arr).sum := by
  have h_pos : ∀ x ∈ arr, 0 < |x| := by
    intro x hx
    apply abs_pos_of_ne_zero
    rw [zero_not_mem_iff_all_ne_zero] at h_nozero
    exact h_nozero x hx
  cases' arr with head tail
  · contradiction
  · simp only [List.map_cons, List.sum_cons]
    apply add_pos
    · exact h_pos head (List.mem_cons_self head tail)
    · by_cases h : tail = []
      · simp [h]
        exact h_pos head (List.mem_cons_self head tail)
      · have h_pos_tail : ∀ x ∈ tail, 0 < |x| := by
          intro x hx
          exact h_pos x (List.mem_cons_of_mem head hx)
        apply List.sum_pos (fun x hx => by
          simp only [List.mem_map] at hx
          obtain ⟨y, hy_mem, hy_eq⟩ := hx
          rw [← hy_eq]
          exact h_pos_tail y hy_mem)
        simp only [List.map_eq_nil]
        exact h

theorem correctness
(arr: List Int)
: problem_spec implementation arr := by
  unfold problem_spec
  simp [implementation]
  split_ifs with h1 h2 h3
  · -- Case: arr = []
    use none
    simp
    exact h1
  · -- Case: arr ≠ [] and has_zero
    use (some 0)
    simp
    constructor
    · constructor
      · simp only [lt_self_iff_false, false_iff]
        intro ⟨⟨_, h_notin⟩, _⟩
        exact h_notin h2
      · simp only [lt_self_iff_false, false_iff]
        intro ⟨⟨_, h_notin⟩, _⟩
        exact h_notin h2
    · constructor
      · exact h2
      · intro h
        rfl
  · -- Case: arr ≠ [] and ¬has_zero and neg_count % 2 = 1
    let magnitude_sum := (arr.map (fun x => Int.ofNat x.natAbs)).sum
    have h_eq : magnitude_sum = (List.map (fun x => |x|) arr).sum := by
      simp only [List.map_map]
      congr 1
      ext x
      rw [abs_of_ofNat_natAbs]
    use (some (-magnitude_sum))
    simp [h_eq]
    constructor
    · constructor
      · constructor
        · constructor
          · simp [h3]
          · exact h2
        · rfl
      · intro ⟨⟨_, _⟩, h_eq_neg⟩
        rw [← h_eq_neg]
        have h_pos : 0 < (List.map (fun x => |x|) arr).sum := sum_pos_of_nonempty_nonzero arr h1 h2
        linarith
    · constructor
      · constructor
        · intro h_gt
          have h_pos : 0 < (List.map (fun x => |x|) arr).sum := sum_pos_of_nonempty_nonzero arr h1 h2
          linarith
        · intro ⟨⟨h_even, _⟩, _⟩
          exfalso
          rw [Nat.mod_two_eq_zero_or_one] at h_even
          cases h_even with
          | inl h => rw [h] at h3; norm_num at h3
          | inr h => rw [h] at h3; norm_num at h3
      · constructor
        · intro h_zero
          have h_pos : 0 < (List.map (fun x => |x|) arr).sum := sum_pos_of_nonempty_nonzero arr h1 h2
          linarith
        · intro h_mem
          exact absurd h_mem h2
  · -- Case: arr ≠ [] and ¬has_zero and neg_count % 2 ≠ 1
    let magnitude_sum := (arr.map (fun x => Int.ofNat x.natAbs)).sum
    have h_eq : magnitude_sum = (List.map (fun x => |x|) arr).sum := by
      simp only [List.map_map]
      congr 1
      ext x
      rw [abs_of_ofNat_natAbs]
    use (some magnitude_sum)
    simp [h_eq]
    constructor
    · constructor
      · intro h_lt
        have h_pos : 0 < (List.map (fun x => |x|) arr).sum := sum_pos_of_nonempty_nonzero arr h1 h2
        linarith
      · intro ⟨⟨h_odd, _⟩, _⟩
        exfalso
        have h_even : (List.filter (fun x => decide (x < 0)) arr).length % 2 = 0 := by
          rw [Nat.mod_two_eq_zero_or_one]
          cases' Nat.mod_two_eq_zero_or_one ((List.filter (fun x => decide (x < 0)) arr).length) with h h
          · exact Or.inl h
          · exfalso
            exact h3 h
        exact h3 h_odd
    · constructor
      · constructor
        · intro h_gt
          constructor
          · constructor
            · rw [Nat.mod_two_eq_zero_or_one]
              cases' Nat.mod_two_eq_zero_or_one ((List.filter (fun x => decide (x < 0)) arr).length) with h h
              · exact Or.inl h
              · exfalso
                exact h3 h
            · exact h2
          · rfl
        · intro ⟨⟨_, _⟩, h_eq_pos⟩
          rw [h_eq_pos]
          exact sum_pos_of_nonempty_nonzero arr h1 h2
      · constructor
        · intro h_zero
          have h_pos : 0 < (List.map (fun x => |x|) arr).sum := sum_pos_of_nonempty_nonzero arr h1 h2
          linarith
        · intro h_mem
          exact absurd h_mem h2