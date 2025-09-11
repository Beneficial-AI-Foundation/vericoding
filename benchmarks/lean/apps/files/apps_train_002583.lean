-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def encode (s : String) : String := sorry 
def decode (s : String) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem encode_length_preserving (s : String) : 
  (encode s).length = s.length := sorry

theorem decode_length_preserving (s : String) :
  (decode s).length = s.length := sorry

theorem encode_non_vowels_unchanged (s : String) :
  ∀ c, c ∈ s.data → c ∉ ['a', 'e', 'i', 'o', 'u'] → 
  c ∈ (encode s).data := sorry

theorem decode_non_numbers_unchanged (s : String) :
  ∀ c, c ∈ s.data → c ∉ ['1', '2', '3', '4', '5'] →
  c ∈ (decode s).data := sorry

/-
info: 'h2ll4'
-/
-- #guard_msgs in
-- #eval encode "hello"

/-
info: 'hello'
-/
-- #guard_msgs in
-- #eval decode "h2ll4"

/-
info: 'H4w 1r2 y45 t4d1y?'
-/
-- #guard_msgs in
-- #eval encode "How are you today?"

/-
info: 'How are you today?'
-/
-- #guard_msgs in
-- #eval decode "H4w 1r2 y45 t4d1y?"

/-
info: 'Th3s 3s 1n 2nc4d3ng t2st.'
-/
-- #guard_msgs in
-- #eval encode "This is an encoding test."

/-
info: 'This is an encoding test.'
-/
-- #guard_msgs in
-- #eval decode "Th3s 3s 1n 2nc4d3ng t2st."
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded