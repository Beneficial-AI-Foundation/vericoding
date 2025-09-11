-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def geometric_sequence_elements (a r n : Int) : String := sorry

theorem geometric_sequence_correct {a r n : Int} (h : n > 0) (hr : r ≠ 0) :
  let terms := (geometric_sequence_elements a r n).splitOn ", ";
  -- sequence has correct length
  terms.length = n
  -- first term is a
  ∧ terms.head? = some (toString a)
  -- each term follows geometric sequence rule
  ∧ ∀ i : Nat, 0 < i → i < n → 
      match terms.get? i, terms.get? (i-1) with
      | some curr, some prev => curr.toInt! = prev.toInt! * r
      | _, _ => False := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_term_sequence {a r : Int} (hr : r ≠ 0) :
  geometric_sequence_elements a r 1 = toString a := sorry

/-
info: '2, 6, 18, 54, 162'
-/
-- #guard_msgs in
-- #eval geometric_sequence_elements 2 3 5

/-
info: '2, 4, 8, 16, 32, 64, 128, 256, 512, 1024'
-/
-- #guard_msgs in
-- #eval geometric_sequence_elements 2 2 10

/-
info: '1, -2, 4, -8, 16, -32, 64, -128, 256, -512'
-/
-- #guard_msgs in
-- #eval geometric_sequence_elements 1 -2 10
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded