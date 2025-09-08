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
def implementation (nums: List Int) : List Int :=
  let indexed := nums.enum
  let sorted := indexed.mergeSort fun (i, x) (j, y) =>
    let sx := digit_sum x
    let sy := digit_sum y
    sx < sy ∨ (sx = sy ∧ i ≤ j)
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
   (sum = head_sum ∧ nums.idxOf num ≥ nums.idxOf head))
  ∧ impl (nums.erase head) = tail
-- program termination
∃ result, impl nums = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma mergeSort_perm {α : Type*} (r : α → α → Bool) (l : List α) : 
  List.Perm l (l.mergeSort r) := by
  sorry

-- LLM HELPER  
lemma map_perm {α β : Type*} (f : α → β) {l1 l2 : List α} (h : List.Perm l1 l2) :
  List.Perm (l1.map f) (l2.map f) := by
  sorry

-- LLM HELPER
lemma enum_map_snd_perm (l : List Int) : List.Perm l (l.enum.map Prod.snd) := by
  sorry

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
      have h1 : List.Perm nums.enum (nums.enum.mergeSort fun (i, x) (j, y) => digit_sum x < digit_sum y ∨ (digit_sum x = digit_sum y ∧ i ≤ j)) := mergeSort_perm _ _
      have h2 : List.Perm (nums.enum.map Prod.snd) ((nums.enum.mergeSort fun (i, x) (j, y) => digit_sum x < digit_sum y ∨ (digit_sum x = digit_sum y ∧ i ≤ j)).map Prod.snd) := map_perm Prod.snd h1
      have h3 : List.Perm nums (nums.enum.map Prod.snd) := enum_map_snd_perm nums
      exact List.Perm.trans h3 h2
    · -- Match case analysis
      cases h : (nums.enum.mergeSort fun (i, x) (j, y) => digit_sum x < digit_sum y ∨ (digit_sum x = digit_sum y ∧ i ≤ j)).map Prod.snd with
      | nil => 
        simp [h]
        sorry
      | cons head tail =>
        simp [h]
        constructor
        · -- ∀ num ∈ nums, ...
          sorry
        · -- impl (nums.erase head) = tail
          sorry