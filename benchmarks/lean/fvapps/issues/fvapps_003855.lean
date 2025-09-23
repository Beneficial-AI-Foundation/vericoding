-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def string_to_array (s : String) : Array String := sorry

theorem string_to_array_split_join
  (words : Array String)
  (h₁ : words.size > 0)
  (h₂ : ∀ (i : Fin words.size), words.get i ≠ "") :
  string_to_array (" ".intercalate words.toList) = words := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem string_to_array_empty :
  string_to_array "" = #[""] := sorry

theorem string_to_array_no_empty_elements
  (s : String)
  (h : s ≠ "")
  (i : Nat)
  (h₂ : i < (string_to_array s).size - 1) :
  ∃ h₃ : i < (string_to_array s).size, 
    (string_to_array s).get ⟨i, h₃⟩ ≠ "" := sorry

/-
info: ['Robin', 'Singh']
-/
-- #guard_msgs in
-- #eval string_to_array "Robin Singh"

/-
info: ['I', 'love', 'arrays', 'they', 'are', 'my', 'favorite']
-/
-- #guard_msgs in
-- #eval string_to_array "I love arrays they are my favorite"

/-
info: ['']
-/
-- #guard_msgs in
-- #eval string_to_array ""
-- </vc-theorems>