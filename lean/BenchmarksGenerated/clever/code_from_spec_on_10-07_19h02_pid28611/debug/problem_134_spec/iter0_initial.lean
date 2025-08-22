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
  s.length = 1 ∧ (let diff := (s.get 0).toLower.toNat - 'a'.toNat; 0 ≤ diff ∧ diff ≤ 25)

def implementation (txt: String) : Bool := 
  let words := txt.splitOn " "
  match words with
  | [] => false
  | [last_word] => is_single_letter last_word
  | head::tail => implementation (String.join tail)

-- LLM HELPER
lemma string_join_single [DecidableEq α] (s : String) : String.join [s] = s := by
  simp [String.join]

-- LLM HELPER
lemma string_join_cons (h : String) (t : List String) : String.join (h :: t) = h ++ String.join t := by
  simp [String.join]

-- LLM HELPER
lemma is_single_letter_correct (s : String) : 
  is_single_letter s = true ↔ (s.length = 1 ∧ (let diff := (s.get 0).toLower.toNat - 'a'.toNat; 0 ≤ diff ∧ diff ≤ 25)) := by
  simp [is_single_letter]
  constructor
  · intro h
    exact h
  · intro h
    exact h

-- LLM HELPER
lemma is_single_letter_false (s : String) : 
  is_single_letter s = false ↔ ¬(s.length = 1 ∧ (let diff := (s.get 0).toLower.toNat - 'a'.toNat; 0 ≤ diff ∧ diff ≤ 25)) := by
  simp [is_single_letter]
  constructor
  · intro h
    exact h
  · intro h
    exact h

theorem correctness
(txt: String)
: problem_spec implementation txt := by
  unfold problem_spec
  let words := txt.splitOn " "
  cases' h : words with
  | nil => 
    simp [implementation]
    use false
    constructor
    · rfl
    · simp [h]
  | cons head tail =>
    cases' tail with
    | nil =>
      simp [implementation]
      use is_single_letter head
      constructor
      · rfl
      · simp [h]
        cases' is_single_letter head with
        | false =>
          simp [is_single_letter_false]
        | true =>
          simp [is_single_letter_correct]
    | cons second rest =>
      simp [implementation]
      have ih : problem_spec implementation (String.join (second :: rest)) := by
        apply correctness
      unfold problem_spec at ih
      obtain ⟨result, h_eq, h_spec⟩ := ih
      use result
      constructor
      · exact h_eq
      · simp [h]
        exact h_spec