-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def digit_all (x : String) : String := sorry

theorem digit_all_only_digits (s : String) :
  let result := digit_all s
  (∀ c ∈ result.data, c.isDigit) ∨ result = "" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem digit_all_preserves_digits (s : String) :
  let result := digit_all s
  String.mk (s.data.filter Char.isDigit) = result := sorry  

theorem digit_all_output_is_subsequence (s : String) :
  let result := digit_all s
  result ≠ "Invalid input !" →
  ∃ l : List Nat, 
    (∀ i j, i < j → i < l.length → j < l.length → l[i]! < l[j]!) ∧ 
    (result.data = l.map (fun i => s.data[i]!)) := sorry

/-
info: '123456'
-/
-- #guard_msgs in
-- #eval digit_all "123abc456"

/-
info: ''
-/
-- #guard_msgs in
-- #eval digit_all ""

/-
info: 'Invalid input !'
-/
-- #guard_msgs in
-- #eval digit_all 123
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded