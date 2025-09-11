-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def problem {α : Type} (x : α) : α ⊕ String := sorry

theorem formula_integers (x : Int) : 
  problem x = Sum.inl (x * 50 + 6) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem formula_floats (x : Float) : 
  problem x = Sum.inl (x * 50 + 6) := sorry

theorem non_numeric_error (x : String ⊕ ByteArray ⊕ List Int) : 
  problem x = Sum.inr "Error" := sorry

/-
info: 'Error'
-/
-- #guard_msgs in
-- #eval problem "hello"

/-
info: 56
-/
-- #guard_msgs in
-- #eval problem 1

/-
info: 6
-/
-- #guard_msgs in
-- #eval problem 0
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded