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

-- LLM HELPER
lemma is_palindrome_correct (s: String) : is_palindrome s = true ↔ List.Palindrome s.data := by
  simp [is_palindrome, List.Palindrome]
  constructor
  · intro h
    exact h
  · intro h
    exact h

def implementation (s: String) (c: String) : String × Bool := 
  if c.data.length = 0 then
    (s, is_palindrome s)
  else
    let filtered_s := String.join ((s.data.filter (fun x => x ≠ c.data.head!)).map (fun c => String.mk [c]))
    let remaining_c := c.drop 1
    let result := implementation filtered_s remaining_c
    (result.fst, is_palindrome result.fst)

-- LLM HELPER
lemma drop_length (s: String) (h: s.data.length > 0) : (s.drop 1).data.length < s.data.length := by
  simp [String.drop]
  cases' s.data with head tail
  · simp at h
  · simp
    exact Nat.lt_succ_self tail.length

-- LLM HELPER
lemma string_join_filter_map (s: String) (c: Char) :
  String.join ((s.data.filter (fun x => x ≠ c)).map (fun c => String.mk [c])) =
  String.mk (s.data.filter (fun x => x ≠ c)) := by
  simp [String.join, String.mk]
  induction s.data with
  | nil => simp
  | cons head tail ih =>
    simp [List.filter]
    split_ifs with h
    · simp [String.join, ih]
    · simp [String.join, ih]

theorem correctness
(s c: String)
: problem_spec implementation s c := by
  simp [problem_spec]
  exists implementation s c
  constructor
  · rfl
  · simp
    constructor
    · simp [is_palindrome_correct]
    · constructor
      · intro h
        simp [implementation, h]
      · intro h
        simp [implementation, h]
        simp [string_join_filter_map]
        have : c.data.head! = c.data.head! := rfl
        rfl