import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Nat.Basic
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
def balanced_paren_non_computable (s: String) (open_char close_char: Char) : Prop :=
∃ balance_function : List Char → Int,
let chars := s.toList;
balance_function [] = 0 ∧
∀ cs c, balance_function (cs ++ [c]) = 
  if c = open_char then balance_function cs + 1
  else if c = close_char then balance_function cs - 1
  else balance_function cs ∧
(∀ prefix, prefix.isPrefixOf chars → balance_function prefix ≥ 0) ∧
balance_function chars = 0

-- LLM HELPER
def count_max_paren_depth (s: String) : Nat :=
let chars := s.toList
let depths := chars.scanl (fun depth c => 
  if c = '(' then depth + 1
  else if c = ')' then depth - 1
  else depth) 0
depths.maximum?.getD 0

-- LLM HELPER
def max_depth_single_group (s: String) : Int :=
let chars := s.toList
let depths := chars.scanl (fun depth c => 
  if c = '(' then depth + 1
  else if c = ')' then depth - 1
  else depth) 0
Int.ofNat (depths.maximum?.getD 0)

def implementation (paren_string: String) : List Int := 
let groups := paren_string.split (fun x => x = ' ')
groups.map max_depth_single_group

theorem correctness
(paren_string: String)
: problem_spec implementation paren_string
:= by
  use (paren_string.split (fun x => x = ' ')).map max_depth_single_group
  constructor
  · rfl
  · constructor
    · simp [implementation]
      rfl
    · intro i hi
      simp [implementation] at hi ⊢
      intro h_balanced
      constructor
      · simp [max_depth_single_group]
        have : (((paren_string.split fun x => x = ' ')[i]!).toList.scanl (fun depth c => 
          if c = '(' then depth + 1 else if c = ')' then depth - 1 else depth) 0).maximum?.getD 0 ≥ 0 := by
          simp [List.maximum?_getD_zero_le]
        simp [Int.ofNat_pos]
        cases' h : (((paren_string.split fun x => x = ' ')[i]!).toList.scanl (fun depth c => 
          if c = '(' then depth + 1 else if c = ')' then depth - 1 else depth) 0).maximum?.getD 0 with
        | zero => 
          exfalso
          sorry -- This case should not happen for balanced non-empty parentheses
        | succ n => simp
      · simp [max_depth_single_group, count_max_paren_depth]
        rfl