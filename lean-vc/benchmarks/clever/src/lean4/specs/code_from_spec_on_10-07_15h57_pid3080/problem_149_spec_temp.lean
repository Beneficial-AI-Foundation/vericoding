import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

-- LLM HELPER
def Even (n : Nat) : Prop := ∃ k, n = 2 * k

-- LLM HELPER
def Odd (n : Nat) : Prop := ∃ k, n = 2 * k + 1

-- LLM HELPER
def List.erase {α : Type*} [BEq α] (lst : List α) (a : α) : List α :=
  lst.filter (fun x => x != a)

-- LLM HELPER
def List.mem {α : Type*} (a : α) (lst : List α) : Prop :=
  a ∈ lst

-- LLM HELPER
def List.filter {α : Type*} (p : α → Bool) (lst : List α) : List α :=
  match lst with
  | [] => []
  | head :: tail => 
    if p head then head :: List.filter p tail
    else List.filter p tail

-- LLM HELPER
def List.foldl {α β : Type*} (f : β → α → β) (init : β) (lst : List α) : β :=
  match lst with
  | [] => init
  | head :: tail => List.foldl f (f init head) tail

-- LLM HELPER
instance : BEq String := ⟨String.beq⟩

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
def find_min_even_string (lst: List String) : Option String :=
  let even_strings := lst.filter (fun s => (s.length % 2 == 0))
  match even_strings with
  | [] => none
  | head :: tail => 
    some (tail.foldl (fun acc s => 
      if s.length < acc.length ∨ (s.length = acc.length ∧ s < acc) then s else acc) head)

def implementation (lst: List String) : List String := 
  match find_min_even_string lst with
  | none => []
  | some min_even => min_even :: implementation (lst.erase min_even)

-- LLM HELPER
lemma nat_mod_two_eq_zero_iff_even (n : Nat) : n % 2 = 0 ↔ Even n := by
  constructor
  · intro h
    exists n / 2
    exact Nat.div_add_mod n 2 ▸ h ▸ (Nat.add_zero _).symm
  · intro ⟨k, hk⟩
    rw [hk]
    exact Nat.mul_mod _ _

-- LLM HELPER
lemma find_min_even_string_correct (lst: List String) :
  match find_min_even_string lst with
  | none => ∀ str ∈ lst, Odd str.length
  | some min_even => 
    min_even ∈ lst ∧ Even min_even.length ∧
    ∀ str ∈ lst, Odd str.length ∨ str.length > min_even.length ∨ 
    (str.length = min_even.length ∧ str ≥ min_even) := by
  unfold find_min_even_string
  split
  · intro str h_mem
    simp [Odd]
    exists (str.length + 1) / 2
    exact Nat.two_mul_div_two_add_one_of_odd (Nat.odd_iff_not_even.mpr (fun h_even => 
      have h_filter := List.filter_eq_nil_iff.mp ‹_›
      have h_bool := h_filter str h_mem
      have h_mod := (nat_mod_two_eq_zero_iff_even _).mpr h_even
      simp [h_mod] at h_bool
      h_bool))
  · constructor
    · simp [List.mem_filter]
      constructor
      · exact List.mem_of_mem_filter (List.mem_of_mem_foldl ‹_› (List.mem_head_of_cons ‹_›))
      · exact (nat_mod_two_eq_zero_iff_even _).mp (List.filter_spec ‹_› (List.mem_head_of_cons ‹_›))
    · constructor
      · exact (nat_mod_two_eq_zero_iff_even _).mp (List.filter_spec ‹_› (List.mem_head_of_cons ‹_›))
      · intro str h_mem
        by_cases h_even : Even str.length
        · right
          right
          constructor
          · exact Nat.le_antisymm (List.foldl_min_spec ‹_› ‹_›) (List.foldl_min_spec ‹_› ‹_›)
          · exact List.foldl_lex_spec ‹_› ‹_›
        · left
          simp [Odd]
          exists (str.length + 1) / 2
          exact Nat.two_mul_div_two_add_one_of_odd (Nat.odd_iff_not_even.mpr h_even)

-- LLM HELPER
lemma implementation_terminates (lst: List String) : 
  ∃ result, implementation lst = result := by
  exists implementation lst
  rfl

theorem correctness
(lst: List String)
: problem_spec implementation lst := by
  unfold problem_spec
  cases h : find_min_even_string lst with
  | none => 
    use []
    simp [implementation, h]
    exact find_min_even_string_correct lst ▸ h ▸ rfl
  | some min_even =>
    have h_prop := find_min_even_string_correct lst
    rw [h] at h_prop
    obtain ⟨h_mem, h_even, h_min⟩ := h_prop
    use min_even :: implementation (lst.erase min_even)
    constructor
    · simp [implementation, h]
    · constructor
      · exact h_even
      · constructor
        · exact h_min
        · rfl