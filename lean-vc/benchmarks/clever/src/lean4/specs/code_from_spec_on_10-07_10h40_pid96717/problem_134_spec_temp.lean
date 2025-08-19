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
  s.length = 1 ∧ 
  let diff := (s.get 0).toLower.toNat - 'a'.toNat
  0 ≤ diff ∧ diff ≤ 25

def implementation (txt: String) : Bool :=
  let words := txt.splitOn " "
  match words with
  | [] => false
  | [last_word] => is_single_letter last_word
  | head::tail => 
    let tail_txt := String.join tail
    implementation tail_txt

-- LLM HELPER
lemma string_join_cons (head : String) (tail : List String) :
  String.join (head :: tail) = head ++ String.join tail := by
  simp [String.join]

-- LLM HELPER
lemma is_single_letter_correct (s : String) :
  is_single_letter s = (s.length = 1 ∧ (let diff := (s.get 0).toLower.toNat - 'a'.toNat; 0 ≤ diff ∧ diff ≤ 25)) := by
  unfold is_single_letter
  simp

theorem correctness
(txt: String)
: problem_spec implementation txt := by
  unfold problem_spec
  let words := txt.splitOn " "
  cases' h : words with
  | nil => 
    use false
    constructor
    · simp [implementation, h]
    · simp [h]
  | cons head tail =>
    cases' tail with
    | nil =>
      use is_single_letter head
      constructor
      · simp [implementation, h]
      · simp [h, is_single_letter_correct]
    | cons tail_head tail_tail =>
      have : (head :: tail_head :: tail_tail).tail = tail_head :: tail_tail := by simp
      use implementation (String.join (tail_head :: tail_tail))
      constructor
      · simp [implementation, h, this]
      · simp [h, this]