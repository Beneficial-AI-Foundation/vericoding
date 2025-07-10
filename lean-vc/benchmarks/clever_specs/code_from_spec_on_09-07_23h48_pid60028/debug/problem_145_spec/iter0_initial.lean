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
def digit_sum (n: Int) : Nat :=
  if n = 0 then 0
  else if n > 0 then
    (n.natAbs.digits 10).sum
  else
    ((-n).natAbs.digits 10).sum

-- LLM HELPER
def find_min_digit_sum (nums: List Int) : Option Int :=
  match nums with
  | [] => none
  | head::tail =>
    let min_rest := find_min_digit_sum tail
    match min_rest with
    | none => some head
    | some rest_min =>
      let head_sum := digit_sum head
      let rest_sum := digit_sum rest_min
      if head_sum < rest_sum then some head
      else if head_sum = rest_sum then
        if nums.indexOf head ≤ nums.indexOf rest_min then some head
        else some rest_min
      else some rest_min

def implementation (nums: List Int) : List Int :=
  match nums with
  | [] => []
  | _ =>
    match find_min_digit_sum nums with
    | none => []
    | some min_elem =>
      min_elem :: implementation (nums.erase min_elem)

-- LLM HELPER
lemma digit_sum_nonneg (n: Int) : digit_sum n ≥ 0 := by
  simp [digit_sum]
  split_ifs <;> simp

-- LLM HELPER
lemma find_min_digit_sum_mem (nums: List Int) (min_elem: Int) :
  find_min_digit_sum nums = some min_elem → min_elem ∈ nums := by
  induction nums with
  | nil => simp [find_min_digit_sum]
  | cons head tail ih =>
    simp [find_min_digit_sum]
    split_ifs with h
    · simp
    · intro h_eq
      cases h_min : find_min_digit_sum tail with
      | none => simp at h_eq; simp [h_eq]
      | some rest_min =>
        simp [h_min] at h_eq
        split_ifs at h_eq with h1 h2
        · simp [h_eq]
        · simp [h_eq]
        · right; exact ih h_min

-- LLM HELPER
lemma implementation_perm (nums: List Int) : List.Perm nums (implementation nums) := by
  induction nums using List.strong_induction_on with
  | ind nums ih =>
    cases nums with
    | nil => simp [implementation]
    | cons head tail =>
      simp [implementation]
      cases h : find_min_digit_sum (head::tail) with
      | none => simp [find_min_digit_sum] at h
      | some min_elem =>
        have mem : min_elem ∈ (head::tail) := find_min_digit_sum_mem (head::tail) min_elem h
        have perm_erase : List.Perm (head::tail) (min_elem :: (head::tail).erase min_elem) := by
          exact List.perm_cons_erase mem
        have smaller : (head::tail).erase min_elem < head::tail := by
          exact List.erase_lt_of_mem mem
        have ih_smaller := ih ((head::tail).erase min_elem) smaller
        exact List.Perm.trans perm_erase (List.Perm.cons min_elem ih_smaller)

-- LLM HELPER
lemma find_min_digit_sum_minimal (nums: List Int) (min_elem: Int) :
  find_min_digit_sum nums = some min_elem →
  ∀ num ∈ nums, digit_sum num > digit_sum min_elem ∨
    (digit_sum num = digit_sum min_elem ∧ nums.indexOf num ≥ nums.indexOf min_elem) := by
  sorry

theorem correctness
(nums: List Int)
: problem_spec implementation nums := by
  simp [problem_spec]
  use implementation nums
  constructor
  · rfl
  · constructor
    · exact implementation_perm nums
    · cases nums with
      | nil => simp [implementation]
      | cons head tail =>
        simp [implementation]
        cases h : find_min_digit_sum (head::tail) with
        | none => simp [find_min_digit_sum] at h
        | some min_elem =>
          constructor
          · exact find_min_digit_sum_minimal (head::tail) min_elem h
          · rfl