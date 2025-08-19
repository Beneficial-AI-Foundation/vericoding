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
def balanced_paren_non_computable (s: String) (open_char: Char) (close_char: Char) : Prop :=
∃ (f : String → Char → Char → Bool), f s open_char close_char = true

-- LLM HELPER
def count_max_paren_depth (s: String) : Nat :=
let chars := s.toList
let rec aux (chars: List Char) (current_depth: Nat) (max_depth: Nat) : Nat :=
  match chars with
  | [] => max_depth
  | c :: rest =>
    if c = '(' then
      let new_depth := current_depth + 1
      aux rest new_depth (max new_depth max_depth)
    else if c = ')' then
      aux rest (current_depth - 1) max_depth
    else
      aux rest current_depth max_depth
aux chars 0 0

-- LLM HELPER
def max_depth_for_group (group: String) : Int :=
Int.ofNat (count_max_paren_depth group)

def implementation (paren_string: String) : List Int :=
let paren_space_split := paren_string.split (fun x => x = ' ')
paren_space_split.map max_depth_for_group

theorem correctness
(paren_string: String)
: problem_spec implementation paren_string
:= by
  unfold problem_spec
  unfold implementation
  simp
  let paren_space_split := paren_string.split (fun x => x = ' ')
  let result := paren_space_split.map max_depth_for_group
  use result
  constructor
  · rfl
  · constructor
    · simp [List.length_map]
    · intro i hi
      intro h_balanced
      simp [max_depth_for_group]
      constructor
      · simp [Int.ofNat_pos]
        apply Nat.succ_pos
      · simp [Int.toNat_of_nonneg]
        simp [Int.ofNat_nonneg]