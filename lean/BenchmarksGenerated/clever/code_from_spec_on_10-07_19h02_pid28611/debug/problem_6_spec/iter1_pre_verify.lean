import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: String → List Int)
-- inputs
(paren_string: String)
:=
-- spec
let spec (result: List Int) :=
let paren_space_split := paren_string.split (fun x => x = ' ');
result.length = paren_space_split.length ∧
∀ i, i < result.length →
let group := paren_space_split[i]!;
balanced_paren_non_computable group '(' ')' →
0 < result[i]! ∧ count_max_paren_depth group = result[i]!.toNat;
-- program termination
∃ result, implementation paren_string = result ∧
spec result

-- LLM HELPER
def balanced_paren_non_computable (s : String) (open : Char) (close : Char) : Prop :=
  let chars := s.toList
  let rec helper (chars : List Char) (depth : Int) : Prop :=
    match chars with
    | [] => depth = 0
    | c :: rest =>
      if c = open then
        helper rest (depth + 1)
      else if c = close then
        depth > 0 ∧ helper rest (depth - 1)
      else
        helper rest depth
  helper chars 0

-- LLM HELPER
def count_max_paren_depth (s : String) : Nat :=
  let chars := s.toList
  let rec helper (chars : List Char) (depth : Nat) (max_depth : Nat) : Nat :=
    match chars with
    | [] => max_depth
    | c :: rest =>
      if c = '(' then
        let new_depth := depth + 1
        helper rest new_depth (max max_depth new_depth)
      else if c = ')' then
        helper rest (depth - 1) max_depth
      else
        helper rest depth max_depth
  helper chars 0 0

-- LLM HELPER
def max_depth_single_group (group : String) : Int :=
  Int.ofNat (count_max_paren_depth group)

def implementation (paren_string: String) : List Int :=
  let paren_space_split := paren_string.split (fun x => x = ' ')
  paren_space_split.map max_depth_single_group

-- LLM HELPER
lemma split_length_eq (s : String) (f : Char → Bool) : 
  (s.split f).length = (s.split f).length := by rfl

-- LLM HELPER
lemma list_get_map {α β : Type*} (f : α → β) (l : List α) (i : Nat) (h : i < l.length) :
  (l.map f)[i]! = f l[i]! := by
  simp [List.getElem!_map, h]

-- LLM HELPER
lemma max_depth_positive (group : String) : 
  balanced_paren_non_computable group '(' ')' → 0 < max_depth_single_group group := by
  intro h
  unfold max_depth_single_group
  simp [Int.ofNat_pos]
  unfold count_max_paren_depth
  sorry -- This would need a more detailed proof about balanced parentheses

-- LLM HELPER
lemma max_depth_correct (group : String) :
  count_max_paren_depth group = (max_depth_single_group group).toNat := by
  unfold max_depth_single_group
  simp [Int.toNat_of_nonneg]

theorem correctness
(paren_string: String)
: problem_spec implementation paren_string
:= by
  unfold problem_spec
  use implementation paren_string
  constructor
  · rfl
  · unfold implementation
    constructor
    · simp [List.length_map]
    · intro i hi
      intro balanced_h
      simp [List.getElem!_map] at hi ⊢
      constructor
      · exact max_depth_positive (paren_string.split (fun x => x = ' '))[i]! balanced_h
      · exact max_depth_correct (paren_string.split (fun x => x = ' '))[i]!