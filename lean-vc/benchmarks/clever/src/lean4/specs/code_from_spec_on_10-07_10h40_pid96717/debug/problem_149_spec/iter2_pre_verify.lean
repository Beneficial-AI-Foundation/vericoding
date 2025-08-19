import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: List String → List String)
-- inputs
(lst: List String) :=
-- spec
let spec (result: List String) :=
match result with
| [] => ∀ str ∈ lst, Odd str.length
| head::tail =>
  Even head.length ∧
  (∀ str ∈ lst,
    Odd str.length ∨
    str.length > head.length ∨
    str.length = head.length ∧ str ≥ head)
  ∧ impl (lst.erase head) = tail
-- program termination
∃ result, impl lst = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def Odd (n : Nat) : Prop := n % 2 = 1

-- LLM HELPER
def Even (n : Nat) : Prop := n % 2 = 0

-- LLM HELPER
def List.filter {α : Type*} (p : α → Bool) (lst : List α) : List α :=
  match lst with
  | [] => []
  | x :: xs => if p x then x :: List.filter p xs else List.filter p xs

-- LLM HELPER
def List.foldl {α β : Type*} (f : β → α → β) (init : β) (lst : List α) : β :=
  match lst with
  | [] => init
  | x :: xs => List.foldl f (f init x) xs

-- LLM HELPER
def List.head! {α : Type*} (lst : List α) : α :=
  match lst with
  | [] => panic! "empty list"
  | x :: _ => x

-- LLM HELPER
def List.erase {α : Type*} [DecidableEq α] (lst : List α) (x : α) : List α :=
  match lst with
  | [] => []
  | y :: ys => if x = y then ys else y :: List.erase ys x

-- LLM HELPER
instance : DecidableEq String := by
  infer_instance

-- LLM HELPER
def find_min_even_string (lst: List String) : Option String :=
  let even_strings := lst.filter (fun s => decide (Even s.length))
  match even_strings with
  | [] => none
  | _ => some (even_strings.foldl (fun acc s => if s.length < acc.length ∨ (s.length = acc.length ∧ s ≤ acc) then s else acc) even_strings.head!)

def implementation (lst: List String) : List String :=
  match find_min_even_string lst with
  | none => []
  | some head => head :: implementation (lst.erase head)

-- LLM HELPER
lemma list_erase_length_lt {α : Type*} [DecidableEq α] (lst : List α) (x : α) (h : x ∈ lst) :
  (lst.erase x).length < lst.length := by
  induction lst with
  | nil => simp at h
  | cons head tail ih =>
    simp [List.erase]
    by_cases h_eq : x = head
    · simp [h_eq]
    · simp [h_eq]
      rw [List.mem_cons] at h
      cases h with
      | inl h_head => contradiction
      | inr h_tail =>
        have : (tail.erase x).length < tail.length := ih h_tail
        omega

-- LLM HELPER
lemma implementation_terminates (lst : List String) : ∃ result, implementation lst = result := by
  use implementation lst
  rfl

theorem correctness
(lst: List String)
: problem_spec implementation lst := by
  unfold problem_spec
  simp only [implementation_terminates]
  use implementation lst
  constructor
  · rfl
  · -- Show that the result satisfies the spec
    induction lst using List.strong_induction with
    | ind lst ih =>
      unfold implementation
      simp only [find_min_even_string]
      let even_strings := lst.filter (fun s => decide (Even s.length))
      cases h : even_strings with
      | nil =>
        -- No even strings, so result is []
        simp
        intro str hstr
        have : ¬Even str.length := by
          by_contra h_even
          have : str ∈ even_strings := by
            simp [even_strings, List.filter]
            constructor
            · exact hstr
            · simp [decide_eq_true_eq]
              exact h_even
          rw [h] at this
          simp at this
        rw [Odd, Even] at this ⊢
        simp at this
        cases Nat.mod_two_eq_zero_or_one str.length with
        | inl h_even => contradiction
        | inr h_odd => exact h_odd
      | cons head tail =>
        -- Found an even string
        simp
        constructor
        · -- head has even length
          have : head ∈ even_strings := by simp [h]
          have : decide (Even head.length) = true := by
            simp [even_strings, List.filter] at this
            exact this.2
          simp [decide_eq_true_eq] at this
          exact this
        constructor
        · -- For all strings in lst, either odd length or length > head.length or equal length and ≥ head
          intro str hstr
          by_cases h_even : Even str.length
          · -- str has even length
            right
            right
            constructor
            · -- This requires showing head is lexicographically minimal
              sorry
            · sorry
          · -- str has odd length
            left
            rw [Odd, Even] at h_even ⊢
            simp at h_even
            cases Nat.mod_two_eq_zero_or_one str.length with
            | inl h_zero => contradiction
            | inr h_one => exact h_one
        · -- Recursive call correctness
          have : head ∈ lst := by
            have : head ∈ even_strings := by simp [h]
            simp [even_strings, List.filter] at this
            exact this.1
          have : (lst.erase head).length < lst.length := by
            apply list_erase_length_lt
            exact this
          exact ih (lst.erase head) this