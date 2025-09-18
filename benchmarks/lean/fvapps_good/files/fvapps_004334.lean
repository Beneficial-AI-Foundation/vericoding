-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def build_a_wall (x y : Int) : Option String := sorry

theorem invalid_input_returns_none {x y : Int} :
  x ≤ 0 ∨ y ≤ 0 → build_a_wall x y = none := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem large_input_returns_resignation {x y : Int} :
  x > 100 ∨ y > 100 → 
  build_a_wall x y = some "Naah, too much...here's my resignation." := sorry

theorem basic_wall_properties {x y : Int} (h1: x > 0) (h2: y > 0) (h3: x * y ≤ 10000) :
  match build_a_wall x y with
  | none => False 
  | some wall => 
    -- Wall is a string with x lines
    let lines := String.split wall (· = '\n')
    lines.length = x ∧
    -- Each line contains the block character
    ∀ line ∈ lines, String.contains line '■'
  := sorry

theorem too_large_wall_returns_resignation {x y : Int} (h1: x > 0) (h2: y > 0) :
  x * y > 10000 →
  build_a_wall x y = some "Naah, too much...here's my resignation." := sorry
-- </vc-theorems>