-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def center_of (s : List Char) : List Char := 
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_and_nonempty (s : List Char) : 
  center_of s = [] ∨ (∀ c, c ∈ center_of s → c ∈ s) :=
sorry 

theorem center_symmetric (s : List Char) (h : s ≠ []) :
  center_of s = (center_of s).reverse :=
sorry

theorem length_bounded (s : List Char) (h : s ≠ []) :
  (center_of s).length ≤ s.length * s.length :=
sorry

theorem result_uses_input_chars (s : List Char) (h : s ≠ []) :
  ∀ c, c ∈ center_of s → c ∈ s :=
sorry

theorem small_alphabet (s : List Char) (h : s ≠ []) 
  (h2 : ∀ c, c ∈ s → c = 'a' ∨ c = 'b') :
  ∀ c, c ∈ center_of s → c = 'a' ∨ c = 'b' :=
sorry

/-
info: ''
-/
-- #guard_msgs in
-- #eval center_of ""

/-
info: 'aba'
-/
-- #guard_msgs in
-- #eval center_of "abc"

/-
info: 'aecea'
-/
-- #guard_msgs in
-- #eval center_of "abcde"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded