-- <vc-helpers>
-- </vc-helpers>

def parse (s : String) : List Int := sorry

def countChar (s : String) (c : Char) : Nat := 
  s.toList.filter (· = c) |>.length

theorem parse_output_bounded (s : String) :
  ∀ x ∈ parse s, x ≥ -s.length
  := sorry

/-
info: [0, 0, 0]
-/
-- #guard_msgs in
-- #eval parse "ooo"

/-
info: [1, 2, 3]
-/
-- #guard_msgs in
-- #eval parse "ioioio"

/-
info: [0, 1]
-/
-- #guard_msgs in
-- #eval parse "idoiido"

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible