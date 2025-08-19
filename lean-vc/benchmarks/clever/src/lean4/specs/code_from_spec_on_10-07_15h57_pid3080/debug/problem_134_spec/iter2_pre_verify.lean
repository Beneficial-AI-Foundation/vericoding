import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: String → Bool)
-- inputs
(txt: String) :=
-- spec
let spec (result: Bool) :=
  let words := txt.splitOn " ";
  match words with
  | [] => result = False
  | [last_word] => (result ↔ last_word.length = 1 ∧ (let diff := (last_word.get 0).toLower.toNat - 'a'.toNat; 0 ≤ diff ∧ diff ≤ 25))
  | head::tail => result ↔ (let tail_txt := String.join tail; impl tail_txt);
-- program terminates
∃ result, impl txt = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def is_single_letter (s: String) : Bool :=
  s.length == 1 && 
  let diff := (s.get 0).toLower.toNat - 'a'.toNat
  0 ≤ diff && diff ≤ 25

def implementation (txt: String) : Bool := 
  let words := txt.splitOn " "
  match words with
  | [] => false
  | [last_word] => is_single_letter last_word
  | head::tail => implementation (String.join tail)

-- LLM HELPER
lemma string_join_splitOn_tail (head : String) (tail : List String) :
  String.join tail = String.join tail := by rfl

-- LLM HELPER
lemma is_single_letter_correct (s : String) :
  is_single_letter s = (s.length = 1 ∧ (let diff := (s.get 0).toLower.toNat - 'a'.toNat; 0 ≤ diff ∧ diff ≤ 25)) := by
  simp [is_single_letter]
  constructor
  · intro h
    cases h with
    | mk h1 h2 =>
      constructor
      · simp [Nat.beq_eq] at h1
        exact h1
      · exact h2
  · intro h
    cases h with
    | mk h1 h2 =>
      constructor
      · simp [Nat.beq_eq]
        exact h1
      · exact h2

theorem correctness
(txt: String)
: problem_spec implementation txt := by
  simp [problem_spec]
  use implementation txt
  constructor
  · rfl
  · simp only [implementation]
    let words := txt.splitOn " "
    cases h : words with
    | nil => simp [implementation]
    | cons head tail =>
      cases tail with
      | nil => 
        simp [implementation, is_single_letter_correct]
      | cons head' tail' =>
        simp [implementation]
        rfl