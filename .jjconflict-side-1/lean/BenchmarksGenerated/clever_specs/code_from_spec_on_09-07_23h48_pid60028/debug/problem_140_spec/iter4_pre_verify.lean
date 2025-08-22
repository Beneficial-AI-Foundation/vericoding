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
        (k ≤ 2 → result = (String.mk (List.replicate k '_')) ++ (impl (text.drop k)))
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
def make_underscores (n: Nat) : String :=
  String.mk (List.replicate n '_')

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
        make_underscores leading_spaces ++ implementation remaining
      else
        "-" ++ implementation remaining
termination_by text.length

-- LLM HELPER
lemma string_drop_decreases (s: String) (h: s ≠ "") : (s.drop 1).length < s.length := by
  have h1 : s.length > 0 := by
    rw [String.length_pos]
    exact h
  simp [String.length_drop]
  omega

-- LLM HELPER
lemma text_drop_spaces_decreases (text: String) (h: text ≠ "") (h_spaces: count_leading_spaces text > 0) : 
  (text.drop (count_leading_spaces text)).length < text.length := by
  have h1 : count_leading_spaces text > 0 := h_spaces
  simp [String.length_drop]
  have h2 : text.length > 0 := by
    rw [String.length_pos]
    exact h
  omega

-- LLM HELPER
lemma count_leading_spaces_correct (text: String) : 
  let k := count_leading_spaces text
  let pref := text.take k
  let suff := text.drop k
  text = pref ++ suff ∧ 
  (k = 0 → pref = "") ∧
  (k > 0 → pref ≠ "" ∧ (∀ ch, ch ∈ pref.toList → ch = ' ')) := by
  simp [String.take_append_drop]
  constructor
  · intro h_zero
    simp [String.take_zero]
  · intro h_pos
    constructor
    · simp [String.take_ne_empty_iff]
      omega
    · intro ch h_mem
      have h_take : (text.take (count_leading_spaces text)).toList = (text.toList.take (count_leading_spaces text)) := by
        simp [String.toList_take]
      rw [h_take] at h_mem
      have : ∀ i, i < count_leading_spaces text → text.toList.get! i = ' ' := by
        intro i h_i
        unfold count_leading_spaces
        have : ∀ (chars: List Char) (count: Nat), 
          (let rec aux (chars: List Char) (count: Nat) : Nat :=
            match chars with
            | [] => count
            | ' ' :: rest => aux rest (count + 1)
            | _ => count
          aux chars count) - count ≤ chars.length := by
          intro chars count
          sorry
        sorry
      sorry

theorem correctness
(text: String) : problem_spec implementation text := by
  unfold problem_spec
  use implementation text
  constructor
  · rfl
  · constructor
    · intro h_empty
      unfold implementation at h_empty
      by_cases h : text = ""
      · exact h
      · simp [h] at h_empty
        exfalso
        by_cases h_leading : count_leading_spaces text = 0
        · simp [h_leading] at h_empty
          have h_nonempty : String.mk [text.get! 0] ≠ "" := by
            simp [String.mk_ne_empty_iff]
          simp [h_nonempty] at h_empty
        · simp [h_leading] at h_empty
          by_cases h_le : count_leading_spaces text ≤ 2
          · simp [h_le] at h_empty
            have : make_underscores (count_leading_spaces text) ≠ "" := by
              unfold make_underscores
              simp [String.mk_ne_empty_iff]
              have : count_leading_spaces text > 0 := by
                omega
              simp [List.replicate_ne_nil_iff]
              omega
            simp [this] at h_empty
          · simp [h_le] at h_empty
            simp at h_empty
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
          simp [String.cons_head_tail h]
          constructor
          · simp [String.length_mk]
          constructor
          · by_contra h_contra
            have : count_leading_spaces text > 0 := by
              unfold count_leading_spaces
              simp [String.get!]
              have : text.length > 0 := by
                rw [String.length_pos]
                exact h
              have : text.toList ≠ [] := by
                simp [String.toList_eq_nil_iff]
                exact h
              cases text.toList with
              | nil => contradiction
              | cons head tail =>
                simp
                exact h_contra
            omega
          · rfl
        · simp [h_leading]
          right
          let k := count_leading_spaces text
          have h_k_pos : k > 0 := by
            unfold k
            omega
          let pref := text.take k
          let suff := text.drop k
          use pref, suff
          constructor
          · simp [String.take_append_drop]
          constructor
          · simp [String.take_ne_empty_iff]
            omega
          constructor
          · intro ch h_mem
            have h_take : pref.toList = (text.toList.take k) := by
              simp [String.toList_take]
            rw [h_take] at h_mem
            have : ∀ i, i < k → text.toList.get! i = ' ' := by
              intro i h_i
              unfold k count_leading_spaces
              sorry
            sorry
          · constructor
            · intro h_le
              simp [h_le]
              unfold k
              simp [make_underscores]
              unfold suff
              rfl
            · intro h_gt
              simp [h_gt]
              unfold suff
              rfl