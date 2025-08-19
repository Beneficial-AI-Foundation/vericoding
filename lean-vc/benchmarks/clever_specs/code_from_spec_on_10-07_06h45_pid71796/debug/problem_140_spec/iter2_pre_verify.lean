def problem_spec
-- function signature
(impl: String → String)
-- inputs
(text: String) :=
-- spec
let spec (result: String) :=
  (result = "" → text = "") ∧
  (result ≠ "" → (
    (∃ pref s, text = pref ++ s
      ∧ pref.length = 1
      ∧ pref ≠ " "
      ∧ result = pref ++ impl s)
    ∨
    (∃ pref s : String, text = pref ++ s ∧ pref ≠ "" ∧ (∀ ch, ch ∈ pref.toList → ch = ' ')
      ∧ let k := pref.length;
        (k ≤ 2 → result = (String.replicate k '_') ++ (impl (text.drop k)))
      ∧ (2 < k → result = "-" ++ (impl (text.drop k)))) )
  )
-- program termination
∃ result, impl text = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def count_leading_spaces (s: String) : Nat :=
  s.toList.takeWhile (· = ' ') |>.length

-- LLM HELPER
def all_spaces (s: String) : Prop :=
  ∀ ch, ch ∈ s.toList → ch = ' '

-- LLM HELPER
lemma all_spaces_takeWhile (s: String) : all_spaces (String.mk (s.toList.takeWhile (· = ' '))) := by
  intro ch h
  simp [String.mk] at h
  exact List.mem_takeWhile.mp h

-- LLM HELPER
lemma takeWhile_spaces_eq (s: String) : 
  String.mk (s.toList.takeWhile (· = ' ')) = s.take (count_leading_spaces s) := by
  simp [count_leading_spaces, String.take]

-- LLM HELPER
lemma string_decomp_spaces (s: String) : 
  s = s.take (count_leading_spaces s) ++ s.drop (count_leading_spaces s) := by
  rw [String.take_append_drop]

-- LLM HELPER
lemma string_take_one_neq_space (s: String) (h: s.get? 0 ≠ some ' ') : s.take 1 ≠ " " := by
  by_contra h_contra
  cases' ht : s.toList with hd tl
  · simp [String.get?] at h
  · simp [String.take, String.get?] at h h_contra
    rw [ht] at h_contra
    simp at h_contra
    rw [ht] at h
    simp at h
    exact h h_contra

-- LLM HELPER
lemma string_take_one_length (s: String) : s.take 1 ≠ "" → s.take 1 |>.length = 1 := by
  intro h
  simp [String.length]
  cases' ht : s.toList with hd tl
  · simp [String.take] at h
  · simp [String.take]

-- LLM HELPER
lemma count_leading_spaces_pos (s: String) (h: s.get? 0 = some ' ') : 0 < count_leading_spaces s := by
  simp [count_leading_spaces]
  cases' ht : s.toList with hd tl
  · simp [String.get?] at h
  · simp [String.get?] at h
    rw [ht] at h
    simp at h
    subst h
    simp [List.takeWhile]

-- LLM HELPER
lemma text_nonempty_of_result_nonempty (text: String) (result: String) 
  (h: result = if text = "" then "" else if text.get? 0 = some ' ' then
    let k := count_leading_spaces text
    if k ≤ 2 then
      String.replicate k '_' ++ result.drop (String.replicate k '_').length
    else
      "-" ++ result.drop 1
  else
    let first_char := text.take 1
    first_char ++ result.drop first_char.length)
  (hr: result ≠ "") : text ≠ "" := by
  by_contra ht
  subst ht
  simp at h
  exact hr h

def implementation (text: String) : String := 
  if text = "" then ""
  else if text.get? 0 = some ' ' then
    let k := count_leading_spaces text
    if k ≤ 2 then
      String.replicate k '_' ++ implementation (text.drop k)
    else
      "-" ++ implementation (text.drop k)
  else
    let first_char := text.take 1
    first_char ++ implementation (text.drop 1)

theorem correctness
(text: String)
: problem_spec implementation text := by
  unfold problem_spec
  use implementation text
  constructor
  · rfl
  · intro result h
    subst h
    constructor
    · intro h
      unfold implementation at h
      split_ifs at h
      · assumption
      · simp at h
      · simp at h
    · intro h
      unfold implementation at h
      split_ifs at h with h1 h2
      · contradiction
      · -- Case: first character is space
        right
        let k := count_leading_spaces text
        use text.take k, text.drop k
        constructor
        · exact string_decomp_spaces text
        constructor
        · -- pref ≠ ""
          simp [String.take_pos_iff]
          constructor
          · exact count_leading_spaces_pos text h2
          · exact String.ne_empty_of_get?_some h2
        constructor
        · -- all chars in pref are spaces
          rw [takeWhile_spaces_eq]
          exact all_spaces_takeWhile text
        · constructor
          · -- k ≤ 2 case
            intro hk
            simp [k] at hk ⊢
            split_ifs at h with h3
            · exact h
            · omega
          · -- 2 < k case
            intro hk
            simp [k] at hk ⊢
            split_ifs at h with h3
            · omega
            · exact h
      · -- Case: first character is not space
        left
        use text.take 1, text.drop 1
        constructor
        · rw [String.take_append_drop]
        constructor
        · -- pref.length = 1
          exact string_take_one_length text h1
        constructor
        · -- pref ≠ " "
          exact string_take_one_neq_space text h2
        · exact h