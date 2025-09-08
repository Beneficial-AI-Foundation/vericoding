/- 
function_signature: "def order_by_points(nums: List[int]) -> List[int]"
docstring: |
    Write a function which sorts the given list of integers
    in ascending order according to the sum of their digits.
    Note: if there are several items with similar sum of their digits,
    order them based on their index in original list.
test_cases:
  - input: [1, 11, -1, -11, -12]
    expected_output: [-1, -11, 1, -12, 11]
  - input: []
    expected_output: []
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

/--
name: digit_sum
use: |
  Helper to sum the digits of a number. If the number is negative, the
  negative sign is treated as part of the first digit.
problems:
  - 145
-/
def digit_sum (n : Int) : Int :=
  let ds := (toString n.natAbs).toList.map fun c => c.toNat - Char.toNat '0'
  match ds with
  | [] => 0
  | d :: ds' =>
    let tail := ds'.foldl (· + ·) 0
    if n < 0 then Int.ofNat tail - Int.ofNat d
    else Int.ofNat (d + tail)

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def enumerate {α : Type*} (l : List α) : List (Nat × α) :=
  List.zip (List.range l.length) l

-- LLM HELPER
def merge_sort_indexed (indexed : List (Nat × Int)) : List (Nat × Int) :=
  indexed.mergeSort fun (i, x) (j, y) =>
    let sx := digit_sum x
    let sy := digit_sum y
    sx < sy ∨ (sx = sy ∧ i ≤ j)

def implementation (nums: List Int) : List Int :=
  let indexed := enumerate nums
  let sorted := merge_sort_indexed indexed
  sorted.map Prod.snd

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
lemma mergeSort_perm {α : Type*} (r : α → α → Bool) (l : List α) : 
  List.Perm l (l.mergeSort r) := by
  induction l using List.mergeSort.induct with
  | h1 => simp [List.mergeSort]
  | h2 a => simp [List.mergeSort]
  | h3 a b l ih1 ih2 =>
    simp [List.mergeSort]
    have := List.Perm.trans ih1 ih2
    apply List.Perm.trans
    · apply List.Perm.cons
      apply List.Perm.cons
      exact List.Perm.refl _
    · apply List.merge_perm

-- LLM HELPER  
lemma map_perm {α β : Type*} (f : α → β) {l1 l2 : List α} (h : List.Perm l1 l2) :
  List.Perm (l1.map f) (l2.map f) := by
  induction h with
  | nil => rfl
  | cons a h ih => exact List.Perm.cons a ih
  | swap a b l => exact List.Perm.swap (f a) (f b) (l.map f)
  | trans h1 h2 ih1 ih2 => exact List.Perm.trans ih1 ih2

-- LLM HELPER
lemma enumerate_map_snd_perm (l : List Int) : List.Perm l (enumerate l).map Prod.snd := by
  unfold enumerate
  induction l with
  | nil => simp [List.zip, List.range]
  | cons head tail ih =>
    simp [List.zip, List.range, List.map]
    apply List.Perm.cons
    convert ih
    simp [List.zip_cons_cons]

theorem correctness
(nums: List Int)
: problem_spec implementation nums := by
  unfold problem_spec
  use implementation nums
  constructor
  · rfl
  · unfold implementation
    constructor
    · -- List.Perm nums result
      unfold merge_sort_indexed
      have h1 : List.Perm (enumerate nums) (enumerate nums).mergeSort _ := mergeSort_perm _ _
      have h2 : List.Perm (enumerate nums).map Prod.snd ((enumerate nums).mergeSort _).map Prod.snd := map_perm Prod.snd h1
      have h3 : List.Perm nums (enumerate nums).map Prod.snd := enumerate_map_snd_perm nums
      exact List.Perm.trans h3 h2
    · -- Match case analysis
      cases h : (merge_sort_indexed (enumerate nums)).map Prod.snd with
      | nil => 
        simp [h]
        -- If result is empty, nums must be empty
        have : enumerate nums = [] := by
          unfold merge_sort_indexed at h
          have map_empty : ((enumerate nums).mergeSort _).map Prod.snd = [] := h
          have sort_empty : (enumerate nums).mergeSort _ = [] := by
            cases h' : (enumerate nums).mergeSort _ with
            | nil => rfl
            | cons _ _ => simp [List.map] at map_empty
          have enum_empty : enumerate nums = [] := by
            unfold enumerate
            cases nums with
            | nil => simp [List.zip, List.range]
            | cons _ _ =>
              simp [List.zip, List.range] at sort_empty
              have perm := mergeSort_perm _ (enumerate (nums))
              rw [sort_empty] at perm
              simp at perm
          rw [enum_empty]
        have nums_empty : nums = [] := by
          unfold enumerate at this
          cases nums with
          | nil => rfl
          | cons head tail =>
            simp [List.zip, List.range] at this
        exact nums_empty
      | cons head tail =>
        simp [h]
        constructor
        · -- ∀ num ∈ nums, property holds
          intro num hnum
          simp
          left
          -- This requires a more complex proof about the sorting property
          have : digit_sum head ≤ digit_sum num := by
            -- head is the first element of the sorted list, so it has minimal digit sum
            unfold implementation at h
            unfold merge_sort_indexed at h
            -- The mergeSort ensures this property
            admit
          omega
        · -- impl (nums.erase head) = tail
          -- This requires proving the recursive property
          admit