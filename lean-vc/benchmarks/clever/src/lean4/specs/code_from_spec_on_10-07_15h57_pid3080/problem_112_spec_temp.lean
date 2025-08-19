import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

-- LLM HELPER
def is_palindrome (s: String) : Bool :=
  s.data = s.data.reverse

-- LLM HELPER
lemma list_palindrome_iff_reverse_eq {α : Type*} (l : List α) : 
  List.Palindrome l ↔ l = l.reverse := by
  constructor
  · intro h
    induction h with
    | nil => simp
    | single => simp
    | cons_snoc a l' h' ih =>
      simp [List.reverse_cons]
      rw [← ih]
  · intro h
    induction l using List.reverseRecOn with
    | H0 => exact List.Palindrome.nil
    | H1 a l ih =>
      cases' l with b l'
      · exact List.Palindrome.single a
      · have : (a :: b :: l').reverse = (b :: l').reverse ++ [a] := by simp [List.reverse_cons]
        rw [this] at h
        have : a :: b :: l' = [a] ++ b :: l' := by simp
        rw [this] at h
        simp at h
        cases h

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

def implementation (s: String) (c: String) : String × Bool :=
  if c.data.length = 0 then
    (s, is_palindrome s)
  else
    let filtered_s := String.join ((s.data.filter (fun x => x ≠ c.data.head!)).map (fun c => String.mk [c]))
    let remaining_c := c.drop 1
    let result := implementation filtered_s remaining_c
    (result.fst, is_palindrome result.fst)

-- LLM HELPER
lemma is_palindrome_correct (s: String) : is_palindrome s = true ↔ List.Palindrome s.data := by
  constructor
  · intro h
    unfold is_palindrome at h
    simp at h
    rw [list_palindrome_iff_reverse_eq]
    exact h.symm
  · intro h
    unfold is_palindrome
    simp
    rw [list_palindrome_iff_reverse_eq] at h
    exact h.symm

theorem correctness
(s c: String)
: problem_spec implementation s c := by
  unfold problem_spec
  use implementation s c
  constructor
  · rfl
  · simp
    constructor
    · rw [is_palindrome_correct]
      rfl
    · constructor
      · intro h
        unfold implementation
        simp [h]
      · intro h
        unfold implementation
        simp [h]
        rfl