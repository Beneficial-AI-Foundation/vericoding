-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def parse (s : String) : List Int := sorry

def countChar (s : String) (c : Char) : Nat := 
  s.toList.filter (· = c) |>.length
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible