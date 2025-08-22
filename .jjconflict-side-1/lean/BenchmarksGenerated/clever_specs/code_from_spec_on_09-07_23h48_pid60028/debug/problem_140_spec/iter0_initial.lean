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
  let rec aux (chars: List Char) (count: Nat) : Nat :=
    match chars with
    | [] => count
    | ' ' :: rest => aux rest (count + 1)
    | _ => count
  aux s.toList 0

-- LLM HELPER
def drop_leading_spaces (s: String) : String :=
  let leading_count := count_leading_spaces s
  s.drop leading_count

def implementation (text: String) : String :=
  if text = "" then ""
  else
    let leading_spaces := count_leading_spaces text
    if leading_spaces = 0 then
      -- First character is not a space
      let first_char := text.get! 0
      let rest := text.drop 1
      String.mk [first_char] ++ implementation rest
    else
      -- We have leading spaces
      let remaining := text.drop leading_spaces
      if leading_spaces ≤ 2 then
        String.replicate leading_spaces '_' ++ implementation remaining
      else
        "-" ++ implementation remaining

-- LLM HELPER
lemma count_leading_spaces_correct (s: String) :
  let k := count_leading_spaces s
  ∃ pref suff, s = pref ++ suff ∧ pref.length = k ∧
  (k = 0 → (s ≠ "" → s.get! 0 ≠ ' ')) ∧
  (k > 0 → (∀ ch, ch ∈ pref.toList → ch = ' ') ∧ (suff ≠ "" → suff.get! 0 ≠ ' ')) := by
  sorry

-- LLM HELPER
lemma implementation_terminates (text: String) :
  ∃ result, implementation text = result := by
  use implementation text
  rfl

theorem correctness
(text: String)
: problem_spec implementation text := by
  unfold problem_spec
  use implementation text
  constructor
  · rfl
  · intro result h_eq
    rw [←h_eq]
    constructor
    · intro h_empty
      unfold implementation at h_empty
      by_cases h : text = ""
      · exact h
      · simp [h] at h_empty
        by_cases h_leading : count_leading_spaces text = 0
        · simp [h_leading] at h_empty
          exfalso
          have : text ≠ "" := h
          have : text.drop 1 ≠ "" ∨ text.drop 1 = "" := by tauto
          cases this with
          | inl h1 => 
            have : implementation (text.drop 1) ≠ "" := by
              sorry
            simp [this] at h_empty
          | inr h1 =>
            have : String.mk [text.get! 0] ≠ "" := by
              simp [String.mk]
            simp [this] at h_empty
        · simp [h_leading] at h_empty
          by_cases h_le : count_leading_spaces text ≤ 2
          · simp [h_le] at h_empty
            sorry
          · simp [h_le] at h_empty
            sorry
    · intro h_nonempty
      unfold implementation
      by_cases h : text = ""
      · simp [h] at h_nonempty
        exact False.elim h_nonempty
      · simp [h]
        by_cases h_leading : count_leading_spaces text = 0
        · simp [h_leading]
          left
          use String.mk [text.get! 0], text.drop 1
          constructor
          · sorry -- text = String.mk [text.get! 0] ++ text.drop 1
          constructor
          · simp [String.length]
          constructor
          · sorry -- text.get! 0 ≠ ' ' because count_leading_spaces = 0
          · rfl
        · simp [h_leading]
          right
          let k := count_leading_spaces text
          use String.replicate k ' ', text.drop k
          constructor
          · sorry -- text = String.replicate k ' ' ++ text.drop k
          constructor
          · sorry -- String.replicate k ' ' ≠ ""
          constructor
          · sorry -- all chars in prefix are spaces
          · constructor
            · intro h_le
              simp [h_le]
              sorry
            · intro h_gt
              simp [h_gt]
              sorry