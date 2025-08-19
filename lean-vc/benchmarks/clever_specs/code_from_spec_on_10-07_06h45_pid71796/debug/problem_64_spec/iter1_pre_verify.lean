def problem_spec
-- function signature
(implementation: String → Nat)
-- inputs
(string: String) :=
let isVowel (c : Char) :=
  let vowels := "aeiouAEIOU"
  vowels.contains c
let isY (c : Char) := c = 'y' ∨ c = 'Y'
-- spec
let spec (result: Nat) :=
string.data.all (fun c => c.isAlpha) →
if string.length = 1 then
  result = if isVowel string.data[0]! ∨ isY string.data[0]! then 1 else 0
else
  result = (if isVowel string.data[0]! then 1 else 0) + implementation (string.drop 1);
-- program termination
∃ result, implementation string = result ∧
spec result

-- LLM HELPER
def isVowel (c : Char) : Bool :=
  let vowels := "aeiouAEIOU"
  vowels.contains c

-- LLM HELPER
def isY (c : Char) : Bool := c = 'y' ∨ c = 'Y'

def implementation (string: String) : Nat :=
  if string.length = 0 then 0
  else if string.length = 1 then
    if isVowel string.data[0]! ∨ isY string.data[0]! then 1 else 0
  else
    (if isVowel string.data[0]! then 1 else 0) + implementation (string.drop 1)

-- LLM HELPER
lemma string_drop_length (s : String) : s.length > 0 → (s.drop 1).length < s.length := by
  intro h
  simp [String.length_drop]
  omega

theorem correctness
(s: String)
: problem_spec implementation s
:= by
  unfold problem_spec
  use implementation s
  constructor
  · rfl
  · intro h_alpha
    simp [implementation]
    by_cases h1 : s.length = 0
    · simp [h1]
      have : s.data = [] := by
        have : s.length = s.data.length := by simp [String.length]
        rw [this] at h1
        exact List.length_eq_zero.mp h1
      simp [this]
      simp [String.data] at h_alpha
      trivial
    · by_cases h2 : s.length = 1
      · simp [h2]
        rfl
      · simp [h1, h2]
        have h_pos : s.length > 0 := by
          by_contra h_neg
          simp at h_neg
          exact h1 h_neg
        have h_gt1 : s.length > 1 := by
          by_contra h_neg
          simp at h_neg
          have : s.length ≤ 1 := h_neg
          have : s.length = 1 := by
            exact Nat.eq_of_le_of_lt_succ this (Nat.lt_succ_of_lt (Nat.pos_of_ne_zero h1))
          exact h2 this
        simp [h_gt1, Nat.not_eq_zero_of_zero_lt h_pos, h2]
        rfl