import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Nat.Basic
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
  let abs_n := Int.natAbs n
  (abs_n.digits 10).sum

-- LLM HELPER
def find_min_element (nums : List Int) : Option Int :=
  match nums with
  | [] => none
  | head :: tail =>
    some (tail.foldl (fun acc x =>
      let acc_sum := digit_sum acc
      let x_sum := digit_sum x
      if x_sum < acc_sum then x
      else if x_sum = acc_sum ∧ nums.indexOf x < nums.indexOf acc then x
      else acc) head)

-- LLM HELPER
lemma find_min_element_mem (nums : List Int) (h : nums ≠ []) :
  ∃ x, find_min_element nums = some x ∧ x ∈ nums := by
  cases nums with
  | nil => contradiction
  | cons head tail =>
    simp [find_min_element]
    use tail.foldl (fun acc x =>
      let acc_sum := digit_sum acc
      let x_sum := digit_sum x
      if x_sum < acc_sum then x
      else if x_sum = acc_sum ∧ (head :: tail).indexOf x < (head :: tail).indexOf acc then x
      else acc) head
    constructor
    · rfl
    · apply List.mem_cons_of_mem
      sorry

-- LLM HELPER
lemma find_min_element_minimal (nums : List Int) (h : nums ≠ []) :
  ∃ x, find_min_element nums = some x ∧ x ∈ nums ∧
  ∀ y ∈ nums, digit_sum y > digit_sum x ∨ 
  (digit_sum y = digit_sum x ∧ nums.indexOf y ≥ nums.indexOf x) := by
  sorry

def implementation (nums: List Int) : List Int :=
  match nums with
  | [] => []
  | _ => 
    match find_min_element nums with
    | none => []
    | some min_elem => min_elem :: implementation (nums.erase min_elem)

theorem correctness
(nums: List Int)
: problem_spec implementation nums := by
  unfold problem_spec
  induction nums using List.strongInductionOn with
  | ind nums ih =>
    cases nums with
    | nil =>
      simp [implementation]
      use []
      constructor
      · rfl
      · constructor
        · simp [List.Perm]
        · simp
    | cons head tail =>
      simp [implementation]
      have h_nonempty : head :: tail ≠ [] := by simp
      obtain ⟨min_elem, h_find, h_mem, h_minimal⟩ := find_min_element_minimal (head :: tail) h_nonempty
      rw [h_find]
      simp
      have h_shorter : (head :: tail).length > ((head :: tail).erase min_elem).length := by
        apply List.length_erase_lt_of_mem h_mem
      obtain ⟨result_tail, h_eq, h_spec⟩ := ih ((head :: tail).erase min_elem) (List.length_erase_lt_of_mem h_mem)
      rw [h_eq]
      use min_elem :: result_tail
      constructor
      · rfl
      · constructor
        · sorry -- prove permutation
        · simp
          constructor
          · exact h_minimal
          · exact h_eq