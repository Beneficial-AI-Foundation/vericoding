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
def List.Palindrome (l : List α) : Prop := l = l.reverse

-- LLM HELPER
def is_palindrome (s : String) : Bool :=
  s.data = s.data.reverse

def implementation (s: String) (c: String) : String × Bool := 
  if c.data.length = 0 then
    (s, is_palindrome s)
  else
    let filtered_s := String.join ((s.data.filter (fun x => x ≠ c.data.head!)).map (fun c => String.mk [c]))
    let recursive_result := implementation filtered_s (c.drop 1)
    recursive_result
termination_by c.data.length

-- LLM HELPER
lemma is_palindrome_correct (s : String) : is_palindrome s = true ↔ List.Palindrome s.data := by
  simp [is_palindrome, List.Palindrome]

-- LLM HELPER
lemma string_join_filter_map (s : String) (ch : Char) :
  String.join ((s.data.filter (fun x => x ≠ ch)).map (fun c => String.mk [c])) = 
  String.mk (s.data.filter (fun x => x ≠ ch)) := by
  simp [String.join, String.mk]
  induction s.data with
  | nil => simp
  | cons h t ih =>
    simp [List.filter, List.map]
    split_ifs with h_eq
    · exact ih
    · simp [String.mk, ih]

-- LLM HELPER
lemma drop_one_length (c : String) : c.data.length > 0 → (c.drop 1).data.length < c.data.length := by
  intro h
  simp [String.drop]
  cases c.data with
  | nil => simp at h
  | cons h t => simp; exact Nat.lt_succ_self _

-- LLM HELPER
lemma implementation_fst_eq (s : String) (c : String) : 
  (c.data.length = 0 → (implementation s c).fst = s) ∧
  (c.data.length > 0 → (implementation s c).fst = (implementation (String.join ((s.data.filter (fun x => x ≠ c.data.head!)).map (fun c => String.mk [c]))) (c.drop 1)).fst) := by
  constructor
  · intro h_empty
    simp [implementation]
    rw [if_pos]
    simp at h_empty ⊢
    exact h_empty
  · intro h_nonempty
    simp [implementation]
    rw [if_neg]
    · simp
    · simp at h_nonempty
      exact Nat.not_eq_zero_of_zero_lt h_nonempty

-- LLM HELPER
lemma implementation_snd_palindrome (s : String) (c : String) :
  (implementation s c).snd = List.Palindrome (implementation s c).fst.data := by
  induction c.data.length using Nat.strong_induction_on generalizing s c with
  | ind n ih =>
    simp [implementation]
    split_ifs with h
    · simp [is_palindrome, List.Palindrome]
    · simp at h
      have h_pos : c.data.length > 0 := Nat.pos_of_ne_zero h
      have h_drop : (c.drop 1).data.length < c.data.length := drop_one_length c h_pos
      have ih_result := ih (c.drop 1).data.length h_drop (String.join ((s.data.filter (fun x => x ≠ c.data.head!)).map (fun c => String.mk [c]))) (c.drop 1)
      exact ih_result

theorem correctness
(s c: String)
: problem_spec implementation s c := by
  simp [problem_spec]
  use implementation s c
  constructor
  · rfl
  · simp
    constructor
    · exact implementation_snd_palindrome s c
    · exact implementation_fst_eq s c