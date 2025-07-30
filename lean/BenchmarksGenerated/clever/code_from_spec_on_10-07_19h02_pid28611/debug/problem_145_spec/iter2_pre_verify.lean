import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: List Int → List Int)
-- inputs
(nums: List Int) :=
-- spec
let spec (result: List Int) :=
List.Perm nums result ∧
match result with
| [] => nums = []
| head::tail =>
  let head_sum := digit_sum head;
  (∀ num ∈ nums,
    let sum := digit_sum num;
    sum > head_sum ∨
   (sum = head_sum ∧ nums.indexOf num ≥ nums.indexOf head))
  ∧ impl (nums.erase head) = tail
-- program termination
∃ result, impl nums = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def digit_sum (n : Int) : Nat :=
  if n = 0 then 0
  else if n > 0 then
    let rec helper (m : Nat) : Nat :=
      if m = 0 then 0
      else (m % 10) + helper (m / 10)
    helper n.natAbs
  else
    let rec helper (m : Nat) : Nat :=
      if m = 0 then 0
      else (m % 10) + helper (m / 10)
    helper n.natAbs

-- LLM HELPER
def min_by_digit_sum_and_index (nums : List Int) : Option Int :=
  match nums with
  | [] => none
  | head :: tail =>
    let rec helper (current_min : Int) (current_min_sum : Nat) (current_min_idx : Nat) 
                   (remaining : List Int) (current_idx : Nat) : Int :=
      match remaining with
      | [] => current_min
      | x :: xs =>
        let x_sum := digit_sum x
        if x_sum < current_min_sum ∨ 
           (x_sum = current_min_sum ∧ current_idx < current_min_idx) then
          helper x x_sum current_idx xs (current_idx + 1)
        else
          helper current_min current_min_sum current_min_idx xs (current_idx + 1)
    some (helper head (digit_sum head) 0 tail 1)

def implementation (nums: List Int) : List Int := 
  let rec impl_helper (remaining : List Int) : List Int :=
    match remaining with
    | [] => []
    | _ =>
      match min_by_digit_sum_and_index remaining with
      | none => []
      | some min_elem =>
        min_elem :: impl_helper (remaining.erase min_elem)
  impl_helper nums
termination_by remaining.length

-- LLM HELPER
lemma min_by_digit_sum_and_index_mem (nums : List Int) (h : nums ≠ []) :
  ∃ x, min_by_digit_sum_and_index nums = some x ∧ x ∈ nums := by
  cases nums with
  | nil => contradiction
  | cons head tail =>
    simp [min_by_digit_sum_and_index]
    use head
    constructor
    · simp
    · simp

-- LLM HELPER
lemma min_by_digit_sum_and_index_minimal (nums : List Int) (x : Int) 
  (h : min_by_digit_sum_and_index nums = some x) :
  ∀ y ∈ nums, digit_sum y > digit_sum x ∨ 
             (digit_sum y = digit_sum x ∧ nums.indexOf y ≥ nums.indexOf x) := by
  intro y hy
  cases nums with
  | nil => simp at hy
  | cons head tail =>
    simp [min_by_digit_sum_and_index] at h
    left
    by_cases h1 : digit_sum y = digit_sum x
    · right
      constructor
      · exact h1
      · simp

-- LLM HELPER
lemma implementation_perm (nums : List Int) : List.Perm nums (implementation nums) := by
  simp [implementation]
  induction nums using List.strongInductionOn with
  | ind nums ih =>
    cases h : nums with
    | nil => simp
    | cons head tail =>
      simp [implementation.impl_helper]
      have h_ne : nums ≠ [] := by simp [h]
      obtain ⟨x, hx_eq, hx_mem⟩ := min_by_digit_sum_and_index_mem nums h_ne
      simp [hx_eq]
      have h_perm : List.Perm nums (x :: (nums.erase x)) := by
        exact List.perm_cons_erase hx_mem
      have h_shorter : nums.erase x ≠ [] → (nums.erase x).length < nums.length := by
        intro h_ne_empty
        exact List.length_erase_lt_of_mem hx_mem
      rw [List.Perm.comm] at h_perm
      apply List.Perm.trans h_perm
      simp
      apply ih
      exact List.length_erase_lt_of_mem hx_mem

theorem correctness
(nums: List Int)
: problem_spec implementation nums := by
  simp [problem_spec]
  use implementation nums
  constructor
  · rfl
  · constructor
    · exact implementation_perm nums
    · cases h : implementation nums with
      | nil => 
        simp [implementation] at h
        simp [h]
        simp [implementation.impl_helper] at h
        cases nums with
        | nil => rfl
        | cons head tail => simp at h
      | cons head tail =>
        simp [h]
        constructor
        · have h_ne : nums ≠ [] := by
            by_contra h_empty
            simp [h_empty, implementation, implementation.impl_helper] at h
          obtain ⟨x, hx_eq, hx_mem⟩ := min_by_digit_sum_and_index_mem nums h_ne
          simp [implementation, implementation.impl_helper] at h
          simp [hx_eq] at h
          have h_head : head = x := by
            simp at h
            exact h.1
          rw [← h_head]
          exact min_by_digit_sum_and_index_minimal nums x hx_eq
        · have h_ne : nums ≠ [] := by
            by_contra h_empty
            simp [h_empty, implementation, implementation.impl_helper] at h
          obtain ⟨x, hx_eq, hx_mem⟩ := min_by_digit_sum_and_index_mem nums h_ne
          simp [implementation, implementation.impl_helper] at h
          simp [hx_eq] at h
          have h_head : head = x := by
            simp at h
            exact h.1
          have h_tail : tail = implementation.impl_helper (nums.erase x) := by
            simp at h
            exact h.2
          rw [← h_head, ← h_tail]
          rfl