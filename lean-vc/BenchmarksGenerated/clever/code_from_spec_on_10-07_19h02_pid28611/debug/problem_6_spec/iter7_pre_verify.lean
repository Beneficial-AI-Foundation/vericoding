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
lemma list_get_map {α β : Type*} [Inhabited α] [Inhabited β] (f : α → β) (l : List α) (i : Nat) (h : i < l.length) :
  (l.map f)[i]! = f l[i]! := by
  rw [List.getElem!_map]

-- LLM HELPER
lemma max_depth_positive (group : String) : 
  balanced_paren_non_computable group '(' ')' → 0 < max_depth_single_group group := by
  intro h
  unfold max_depth_single_group
  simp [Int.ofNat_pos]
  unfold count_max_paren_depth
  by_cases h_empty : group.toList = []
  · unfold balanced_paren_non_computable at h
    simp [h_empty] at h
    norm_num
  · by_cases h_has_open : '(' ∈ group.toList
    · simp
      apply Nat.zero_lt_of_ne_zero
      intro h_zero
      have this : count_max_paren_depth group = 0 := by 
        unfold count_max_paren_depth
        simp [h_zero]
      exfalso
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp h_has_open
      have : ∃ j, j < group.toList.length ∧ group.toList.get ⟨j, by exact i.isLt⟩ = '(' := by
        use i.val
        exact ⟨i.isLt, hi⟩
      norm_num
    · simp
      apply Nat.zero_lt_of_ne_zero
      intro h_zero
      norm_num

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
      have h_len : i < (paren_string.split (fun x => x = ' ')).length := by
        simp [List.length_map] at hi
        exact hi
      constructor
      · rw [list_get_map max_depth_single_group (paren_string.split (fun x => x = ' ')) i h_len]
        apply max_depth_positive
        exact balanced_h
      · rw [list_get_map max_depth_single_group (paren_string.split (fun x => x = ' ')) i h_len]
        simp [Int.toNat_of_nonneg]
        exact max_depth_correct (paren_string.split (fun x => x = ' '))[i]!