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

-- LLM HELPER
lemma string_join_tail_shorter (txt : String) (head : String) (tail : List String) :
  head :: tail = txt.splitOn " " → tail ≠ [] → (String.join tail).length < txt.length := by
  intros h_split h_nonempty
  have : txt.length > 0 := by
    rw [← h_split]
    simp [String.splitOn]
    omega
  omega

def implementation (txt: String) : Bool := 
  let words := txt.splitOn " "
  match words with
  | [] => false
  | [last_word] => is_single_letter last_word
  | head::tail => 
    if tail = [] then false
    else implementation (String.join tail)
termination_by txt.length
decreasing_by
  simp_wf
  have h_ne : tail ≠ [] := by simp_all
  have h_split : head :: tail = txt.splitOn " " := by rfl
  apply string_join_tail_shorter
  · exact h_split
  · exact h_ne

-- LLM HELPER
lemma is_single_letter_correct (s : String) : 
  is_single_letter s = true ↔ (s.length = 1 ∧ (let diff := (s.get 0).toLower.toNat - 'a'.toNat; 0 ≤ diff ∧ diff ≤ 25)) := by
  simp [is_single_letter]

theorem correctness
(txt: String)
: problem_spec implementation txt := by
  unfold problem_spec
  let words := txt.splitOn " "
  cases' h : words with
  | nil => 
    simp [implementation]
    use false
    simp [h]
  | cons head tail =>
    cases' tail with
    | nil =>
      simp [implementation]
      use is_single_letter head
      constructor
      · rfl
      · simp [h]
        exact is_single_letter_correct head
    | cons second rest =>
      simp [implementation]
      have tail_nonempty : second :: rest ≠ [] := by simp
      have ih : problem_spec implementation (String.join (second :: rest)) := by
        apply correctness
      unfold problem_spec at ih
      obtain ⟨result, h_eq, h_spec⟩ := ih
      use result
      constructor
      · rw [if_neg tail_nonempty]
        exact h_eq
      · simp [h]
        rw [← h_eq]
        exact h_spec