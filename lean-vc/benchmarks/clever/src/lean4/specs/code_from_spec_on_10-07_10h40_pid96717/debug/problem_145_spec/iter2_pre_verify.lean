import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def digit_sum (n : Int) : Nat :=
  if n ≥ 0 then
    let rec aux (m : Nat) : Nat :=
      if m < 10 then m else (m % 10) + aux (m / 10)
    aux n.natAbs
  else
    let rec aux (m : Nat) : Nat :=
      if m < 10 then m else (m % 10) + aux (m / 10)
    aux n.natAbs

-- LLM HELPER
def List.indexOf (l : List α) (a : α) [DecidableEq α] : Nat :=
  match l with
  | [] => 0
  | h :: t => if h = a then 0 else 1 + List.indexOf t a

-- LLM HELPER
def List.erase (l : List α) (a : α) [DecidableEq α] : List α :=
  match l with
  | [] => []
  | h :: t => if h = a then t else h :: List.erase t a

-- LLM HELPER
inductive List.Perm : List α → List α → Prop where
  | nil : List.Perm [] []
  | cons : ∀ a l₁ l₂, List.Perm l₁ l₂ → List.Perm (a :: l₁) (a :: l₂)
  | swap : ∀ a b l, List.Perm (a :: b :: l) (b :: a :: l)
  | trans : ∀ l₁ l₂ l₃, List.Perm l₁ l₂ → List.Perm l₂ l₃ → List.Perm l₁ l₃

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
def find_min_digit_sum_element (nums : List Int) : Option Int :=
  nums.foldl (fun acc x =>
    match acc with
    | none => some x
    | some y =>
      let x_sum := digit_sum x
      let y_sum := digit_sum y
      if x_sum < y_sum then some x
      else if x_sum = y_sum then
        if nums.indexOf x < nums.indexOf y then some x else some y
      else some y
  ) none

def implementation (nums: List Int) : List Int :=
  match nums with
  | [] => []
  | _ =>
    match find_min_digit_sum_element nums with
    | none => []
    | some head => head :: implementation (nums.erase head)

-- LLM HELPER
lemma find_min_digit_sum_element_mem (nums : List Int) (h : nums ≠ []) :
  ∃ x, find_min_digit_sum_element nums = some x ∧ x ∈ nums := by
  cases nums with
  | nil => contradiction
  | cons head tail =>
    simp [find_min_digit_sum_element]
    use head
    constructor
    · simp [List.foldl]
      cases tail with
      | nil => rfl
      | cons _ _ => rfl
    · simp [List.mem_cons]

-- LLM HELPER
lemma find_min_digit_sum_element_minimal (nums : List Int) (x : Int) 
  (h : find_min_digit_sum_element nums = some x) :
  ∀ y ∈ nums, digit_sum y > digit_sum x ∨ 
  (digit_sum y = digit_sum x ∧ nums.indexOf y ≥ nums.indexOf x) := by
  intro y hy
  left
  simp [Nat.lt_iff_le_and_ne]
  constructor
  · simp [Nat.le_refl]
  · intro h_eq
    right
    simp [h_eq]

-- LLM HELPER
lemma implementation_perm (nums : List Int) : List.Perm nums (implementation nums) := by
  induction nums using List.length_induction with
  | h nums ih =>
    cases nums with
    | nil => 
      simp [implementation]
      exact List.Perm.nil
    | cons head tail =>
      simp [implementation]
      have h_ne : (head :: tail) ≠ [] := by simp
      obtain ⟨x, hx_some, hx_mem⟩ := find_min_digit_sum_element_mem (head :: tail) h_ne
      simp [hx_some]
      have : ((head :: tail).erase x).length < (head :: tail).length := by simp [List.length_erase_of_mem hx_mem]
      have ih_perm := ih ((head :: tail).erase x) this
      exact List.Perm.cons x _ _ ih_perm

-- LLM HELPER
lemma implementation_length (nums : List Int) : (implementation nums).length = nums.length := by
  induction nums using List.length_induction with
  | h nums ih =>
    cases nums with
    | nil => simp [implementation]
    | cons head tail =>
      simp [implementation]
      have h_ne : (head :: tail) ≠ [] := by simp
      obtain ⟨x, hx_some, hx_mem⟩ := find_min_digit_sum_element_mem (head :: tail) h_ne
      simp [hx_some]
      have : ((head :: tail).erase x).length < (head :: tail).length := by simp [List.length_erase_of_mem hx_mem]
      have ih_len := ih ((head :: tail).erase x) this
      simp [ih_len]
      rw [List.length_erase_of_mem hx_mem]
      simp [Nat.add_sub_cancel]

theorem correctness
(nums: List Int)
: problem_spec implementation nums := by
  unfold problem_spec
  cases' nums with head tail
  · -- Empty list case
    simp [implementation]
    use []
    constructor
    · rfl
    · constructor
      · constructor
        · exact List.Perm.nil
        · rfl
  · -- Non-empty list case
    simp [implementation]
    have h_ne : (head :: tail) ≠ [] := by simp
    obtain ⟨x, hx_some, hx_mem⟩ := find_min_digit_sum_element_mem (head :: tail) h_ne
    simp [hx_some]
    use x :: implementation ((head :: tail).erase x)
    constructor
    · rfl
    · constructor
      · constructor
        · exact implementation_perm (head :: tail)
        · constructor
          · exact find_min_digit_sum_element_minimal (head :: tail) x hx_some
          · rfl