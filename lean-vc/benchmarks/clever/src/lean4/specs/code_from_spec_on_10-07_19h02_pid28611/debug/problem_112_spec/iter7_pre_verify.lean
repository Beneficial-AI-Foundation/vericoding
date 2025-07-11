import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: String → String → (String × Bool))
(s: String)
(c: String) :=
let spec (result : String × Bool) :=
  let (result_str, result_bool) := result
  result_bool = (List.Palindrome result_str.data) ∧
  (c.data.length = 0 → result_str = s) ∧
  (c.data.length > 0 →
    result_str =
    (implementation
      (String.join ((s.data.filter (fun x => x ≠ c.data.head!)).map (fun c => String.mk [c])))
      (c.drop 1)).fst)
∃ result,
  implementation s c = result ∧
  spec result

-- LLM HELPER
def filter_string (s: String) (ch: Char) : String :=
  String.join ((s.data.filter (fun x => x ≠ ch)).map (fun c => String.mk [c]))

-- LLM HELPER
def is_palindrome (s: String) : Bool :=
  decide (s.data.reverse = s.data)

def implementation (s: String) (c: String) : String × Bool :=
  if c.data.length = 0 then
    (s, is_palindrome s)
  else
    let filtered := filter_string s c.data.head!
    let (result_str, _) := implementation filtered (c.drop 1)
    (result_str, is_palindrome result_str)
termination_by c.data.length
decreasing_by
  simp [String.drop]
  have h_drop : c.data.length > 0 := by
    by_contra h
    simp at h
    have : c.data.length = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_not_gt h)
    contradiction
  rw [String.drop_data]
  simp [List.length_drop]
  omega

-- LLM HELPER
lemma is_palindrome_correct (s: String) : is_palindrome s = List.Palindrome s.data := by
  simp [is_palindrome, List.Palindrome]
  rw [decide_eq_true_iff]
  constructor
  · intro h
    exact h
  · intro h
    exact h

-- LLM HELPER
lemma filter_string_correct (s: String) (ch: Char) :
  filter_string s ch = String.join ((s.data.filter (fun x => x ≠ ch)).map (fun c => String.mk [c])) := by
  rfl

-- LLM HELPER
lemma implementation_fst_recursive (s c: String) (h: c.data.length > 0) :
  let filtered := filter_string s c.data.head!
  (implementation s c).fst = (implementation filtered (c.drop 1)).fst := by
  simp [implementation]
  have h_ne_zero : ¬c.data.length = 0 := by omega
  simp [h_ne_zero]

-- LLM HELPER
lemma implementation_snd_correct (s c: String) :
  (implementation s c).snd = is_palindrome (implementation s c).fst := by
  induction c using String.rec with
  | mk l =>
    cases l with
    | nil =>
      simp [implementation, is_palindrome, String.mk]
    | cons head tail =>
      simp [implementation, String.mk]
      have h_pos : (String.mk (head :: tail)).data.length > 0 := by simp [String.mk]
      have h_ne_zero : ¬(String.mk (head :: tail)).data.length = 0 := by omega
      simp [h_ne_zero]

theorem correctness
(s c: String)
: problem_spec implementation s c := by
  unfold problem_spec
  use implementation s c
  constructor
  · rfl
  · simp only [true_and]
    constructor
    · rw [implementation_snd_correct]
      rw [is_palindrome_correct]
    · constructor
      · intro h
        simp [implementation, h]
      · intro h
        have h_ne_zero : ¬c.data.length = 0 := by omega
        rw [implementation_fst_recursive s c h]
        rw [filter_string_correct]