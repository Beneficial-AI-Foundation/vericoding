import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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
   (sum = head_sum ∧ List.indexOf num nums ≥ List.indexOf head nums))
  ∧ impl (nums.erase head) = tail
-- program termination
∃ result, impl nums = result ∧
-- return value satisfies spec
spec result

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
termination_by remaining => remaining.length
decreasing_by 
  simp_wf
  cases remaining with
  | nil => contradiction
  | cons head tail =>
    simp [min_by_digit_sum_and_index]
    exact List.length_erase_lt_of_mem (List.mem_cons_self head tail)

-- LLM HELPER
lemma min_by_digit_sum_and_index_mem (nums : List Int) (h : nums ≠ []) :
  ∃ x, min_by_digit_sum_and_index nums = some x ∧ x ∈ nums := by
  cases nums with
  | nil => contradiction
  | cons head tail =>
    simp [min_by_digit_sum_and_index]
    use (min_by_digit_sum_and_index.helper head (digit_sum head) 0 tail 1)
    constructor
    · rfl
    · have h_mem : min_by_digit_sum_and_index.helper head (digit_sum head) 0 tail 1 = head ∨
                   min_by_digit_sum_and_index.helper head (digit_sum head) 0 tail 1 ∈ tail := by
        induction tail generalizing head with
        | nil => simp [min_by_digit_sum_and_index.helper]; left; rfl
        | cons x xs ih =>
          simp [min_by_digit_sum_and_index.helper]
          by_cases h : digit_sum x < digit_sum head ∨ 
                       (digit_sum x = digit_sum head ∧ 1 < 0)
          · simp [h]
            right
            exact ih
          · simp [h]
            left
            rfl
      cases h_mem with
      | inl h_eq => rw [h_eq]; simp
      | inr h_in => exact List.mem_cons_of_mem _ h_in

-- LLM HELPER
lemma min_by_digit_sum_and_index_minimal (nums : List Int) (x : Int) 
  (h : min_by_digit_sum_and_index nums = some x) :
  ∀ y ∈ nums, digit_sum y > digit_sum x ∨ 
             (digit_sum y = digit_sum x ∧ List.indexOf y nums ≥ List.indexOf x nums) := by
  intro y hy
  cases nums with
  | nil => simp at h
  | cons head tail =>
    simp [min_by_digit_sum_and_index] at h
    by_cases h1 : digit_sum y ≤ digit_sum x
    · by_cases h2 : digit_sum y = digit_sum x
      · right
        constructor
        · exact h2
        · by_contra h_contra
          simp at h_contra
          have h_lt : List.indexOf y nums < List.indexOf x nums := Nat.lt_of_not_ge h_contra
          have h_eq : digit_sum y = digit_sum x := h2
          have h_mem_y : y ∈ nums := hy
          have h_mem_x : x ∈ nums := by
            obtain ⟨_, _, hx_mem⟩ := min_by_digit_sum_and_index_mem nums (by simp)
            rw [← h] at hx_mem
            exact hx_mem
          simp
      · left
        exact Nat.lt_of_le_of_ne h1 h2
    · left
      exact Nat.lt_of_not_ge h1

-- LLM HELPER
lemma implementation_perm (nums : List Int) : List.Perm nums (implementation nums) := by
  simp [implementation]
  induction nums using List.strongInductionOn with
  | ind nums ih =>
    cases h : nums with
    | nil => simp [implementation.impl_helper]
    | cons head tail =>
      simp [implementation.impl_helper]
      have h_ne : nums ≠ [] := by simp [h]
      obtain ⟨x, hx_eq, hx_mem⟩ := min_by_digit_sum_and_index_mem nums h_ne
      simp [hx_eq]
      have h_perm : List.Perm nums (x :: (nums.erase x)) := by
        exact List.perm_cons_erase hx_mem
      have h_shorter : (nums.erase x).length < nums.length := by
        exact List.length_erase_lt_of_mem hx_mem
      rw [List.Perm.comm] at h_perm
      apply List.Perm.trans h_perm
      simp
      apply ih
      exact h_shorter

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