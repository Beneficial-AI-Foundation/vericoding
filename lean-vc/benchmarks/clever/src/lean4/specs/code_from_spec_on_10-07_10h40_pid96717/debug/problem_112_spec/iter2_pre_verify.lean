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
def is_palindrome (s: String) : Bool :=
  s.data = s.data.reverse

def implementation (s: String) (c: String) : String × Bool := 
  if c.data.length = 0 then
    (s, is_palindrome s)
  else
    let filtered_s := String.join ((s.data.filter (fun x => x ≠ c.data.head!)).map (fun c => String.mk [c]))
    let recursive_result := implementation filtered_s (c.drop 1)
    (recursive_result.fst, is_palindrome recursive_result.fst)

-- LLM HELPER
lemma is_palindrome_correct (s: String) : 
  is_palindrome s = true ↔ List.Palindrome s.data := by
  simp [is_palindrome, List.Palindrome]
  exact List.eq_reverse_iff_palindrome

theorem correctness
(s c: String)
: problem_spec implementation s c := by
  simp [problem_spec]
  use implementation s c
  constructor
  · rfl
  · simp
    constructor
    · rw [← is_palindrome_correct]
      simp [implementation]
      split_ifs <;> simp
    · constructor
      · intro h
        simp [implementation, h]
      · intro h
        simp [implementation, h]