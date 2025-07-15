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

def implementation (s: String) (c: String) : String × Bool :=
  if c.data.length = 0 then
    (s, List.Palindrome s.data)
  else
    let filtered := filter_string s c.data.head!
    let (result_str, _) := implementation filtered (c.drop 1)
    (result_str, List.Palindrome result_str.data)

-- LLM HELPER
lemma filter_string_correct (s: String) (ch: Char) :
  filter_string s ch = String.join ((s.data.filter (fun x => x ≠ ch)).map (fun c => String.mk [c])) := by
  rfl

-- LLM HELPER
lemma string_drop_length (s: String) : s.data.length > 0 → (s.drop 1).data.length = s.data.length - 1 := by
  intro h
  simp [String.drop]
  cases' s.data with hd tl
  · simp at h
  · simp [List.length]

-- LLM HELPER
lemma implementation_preserves_spec (s c: String) :
  let result := implementation s c
  let (result_str, result_bool) := result
  result_bool = List.Palindrome result_str.data := by
  simp [implementation]
  split_ifs with h
  · simp
  · simp

theorem correctness
(s c: String)
: problem_spec implementation s c := by
  unfold problem_spec
  use implementation s c
  constructor
  · rfl
  · simp only [true_and]
    constructor
    · exact implementation_preserves_spec s c
    · constructor
      · intro h
        simp [implementation, h]
      · intro h
        simp [implementation, h]
        have : c.data.head! ∈ c.data := by
          cases' c.data with hd tl
          · simp at h
          · simp [List.head!]
        simp [filter_string_correct]