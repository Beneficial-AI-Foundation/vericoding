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
def string_length_after_join (words : List String) : Nat :=
  words.foldl (fun acc s => acc + s.length) 0

def implementation (txt: String) : Bool := 
  let words := txt.splitOn " "
  match words with
  | [] => false
  | [last_word] => is_single_letter last_word
  | _::tail => implementation (String.join tail)
termination_by string_length_after_join (txt.splitOn " ")
decreasing_by
  simp_wf
  simp [string_length_after_join]
  have : (List.foldl (fun acc s => acc + s.length) 0 tail : Nat) < 
         (List.foldl (fun acc s => acc + s.length) 0 (txt.splitOn " ") : Nat) := by
    have split_nonempty : txt.splitOn " " ≠ [] := by
      intro h
      cases' txt.splitOn " " with
      | nil => simp at h
      | cons _ _ => simp at h
    sorry
  exact this

-- LLM HELPER
lemma string_join_single (s : String) : String.join [s] = s := by
  simp [String.join, List.foldl]

-- LLM HELPER
lemma string_join_cons (h : String) (t : List String) : String.join (h :: t) = h ++ String.join t := by
  simp [String.join, List.foldl]

-- LLM HELPER
lemma is_single_letter_correct (s : String) : 
  is_single_letter s = true ↔ (s.length = 1 ∧ (let diff := (s.get 0).toLower.toNat - 'a'.toNat; 0 ≤ diff ∧ diff ≤ 25)) := by
  simp [is_single_letter]

-- LLM HELPER
lemma is_single_letter_false (s : String) : 
  is_single_letter s = false ↔ ¬(s.length = 1 ∧ (let diff := (s.get 0).toLower.toNat - 'a'.toNat; 0 ≤ diff ∧ diff ≤ 25)) := by
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
      · simp [h, string_join_single]
        exact is_single_letter_correct head
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
        rw [← h_eq]
        exact h_spec